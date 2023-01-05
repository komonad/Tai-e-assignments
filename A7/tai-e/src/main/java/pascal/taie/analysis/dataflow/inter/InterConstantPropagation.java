/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.inter;

import java.util.HashMap;
import java.util.Map;

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.StaticFieldAccess;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    private final HashMap<JField, Value> staticField;
    private final Map<Var, Map<JField, Value>> instanceFields;
    private final Map<Var, Map<Value, Value>> arrayAccess;

    private PointerAnalysisResult pta;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
        staticField = new HashMap<>();
        instanceFields = new HashMap<>();
        arrayAccess = new HashMap<>();
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        pta = World.get().getResult(ptaId);
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
//        var oldOut = out.copy();
        out.clear();
        out.copyFrom(in);
        return true;
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        if (stmt instanceof LoadField loadField &&
            ConstantPropagation.canHoldInt(loadField.getLValue()) &&
            loadField.getRValue() instanceof InstanceFieldAccess ifa) {
            var field = ifa.getFieldRef().resolve();
            var pointsTo = pta.getPointsToSet(ifa.getBase());
            var value = pta.getVars().stream()
                .filter(v -> pta.getPointsToSet(v).stream().anyMatch(pointsTo::contains))
                .map(v -> instanceFields.computeIfAbsent(v, k -> new HashMap<>())
                    .computeIfAbsent(field, k -> Value.getUndef())
                )
                .reduce(Value.getUndef(), cp::meetValue);
            var oldOut = out.copy();
            out.copyFrom(in);
            out.update(loadField.getLValue(), value);
            return !out.equals(oldOut);
        } else if (stmt instanceof LoadField loadField &&
            ConstantPropagation.canHoldInt(loadField.getLValue()) &&
            loadField.getRValue() instanceof StaticFieldAccess sfa) {
            var value = staticField.get(loadField.getFieldRef().resolve());
            if (value == null) {
                value = Value.getUndef();
            }
            var oldOut = out.copy();
            out.copyFrom(in);
            out.update(loadField.getLValue(), value);
            return !out.equals(oldOut);
        } else if (stmt instanceof LoadArray loadArray &&
            ConstantPropagation.canHoldInt(loadArray.getLValue())) {
            var pointsTo = pta.getPointsToSet(loadArray.getRValue().getBase());
            var idx = ConstantPropagation.evaluate(loadArray.getRValue().getIndex(), in);
            var value = pta.getVars().stream()
                .filter(v -> pta.getPointsToSet(v).stream().anyMatch(pointsTo::contains))
                .flatMap(v -> arrayAccess.getOrDefault(v, new HashMap<>()).entrySet().stream())
                .filter(v -> {
                    var targetIdx = v.getKey();
                    if (targetIdx.isUndef() || idx.isUndef()) return false;
                    if (targetIdx.isNAC() || idx.isNAC()) return true;
                    return targetIdx.getConstant() == idx.getConstant();
                })
                .map(Map.Entry::getValue)
                .reduce(Value.getUndef(), cp::meetValue);
            var oldOut = out.copy();
            out.copyFrom(in);
            out.update(loadArray.getLValue(), value);
            return !out.equals(oldOut);
        } else if (stmt instanceof StoreField storeField && storeField.isStatic() &&
            ConstantPropagation.canHoldInt(storeField.getRValue())) {
            var field = storeField.getFieldRef().resolve();
            var oldValue = staticField.computeIfAbsent(field, k -> Value.getUndef());
            var value = ConstantPropagation.evaluate(storeField.getRValue(), in);
            var newValue = cp.meetValue(value, oldValue);
            staticField.put(field, newValue);
            var oldOut = out.copy();
            out.copyFrom(in);
            if (!oldValue.equals(newValue)) {
                solver.addAll();
            }
            return !oldOut.equals(out);
        } else if (stmt instanceof StoreField storeField &&
            storeField.getFieldAccess() instanceof InstanceFieldAccess ifa &&
            ConstantPropagation.canHoldInt(storeField.getRValue())) {
            var obj = ifa.getBase();
            var field = ifa.getFieldRef().resolve();
            var varMap = instanceFields.computeIfAbsent(obj, k -> new HashMap<>());
            var oldValue = varMap.getOrDefault(field, Value.getUndef());
            var value = ConstantPropagation.evaluate(storeField.getRValue(), in);
            var newValue = cp.meetValue(value, oldValue);
            varMap.put(field, newValue);
            var oldOut = out.copy();
            out.copyFrom(in);
            if (!oldValue.equals(newValue)) {
                solver.addAll();
            }
            return !oldOut.equals(out);
        } else if (stmt instanceof StoreArray storeArray &&
            ConstantPropagation.canHoldInt(storeArray.getRValue())) {
            var obj = storeArray.getLValue().getBase();
            var idx = ConstantPropagation.evaluate(storeArray.getLValue().getIndex(), in);
            var arrayMap = arrayAccess.computeIfAbsent(obj, k -> new HashMap<>());
            var oldValue = arrayMap.getOrDefault(idx, Value.getUndef());
            var value = ConstantPropagation.evaluate(storeArray.getRValue(), in);
            var newValue = cp.meetValue(value, oldValue);
            arrayMap.put(idx, newValue);
            var oldOut = out.copy();
            out.copyFrom(in);
            if (!oldValue.equals(newValue)) {
                solver.addAll();
            }
            return !oldOut.equals(out);
        }
        return cp.transferNode(stmt, in, out);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        CPFact fact = out.copy();
        var stmt = edge.getSource();
        if (stmt instanceof Invoke i && i.getLValue() != null) {
            fact.remove(i.getLValue());
        }
        return fact;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        var newFact = cp.newInitialFact();

        var source = edge.getSource();
        var invoke = (Invoke) source;
        var method = edge.getCallee();

        for (int i = 0; i < invoke.getRValue().getArgs().size(); i++) {
            newFact.update(method.getIR().getParam(i), callSiteOut.get(invoke.getRValue().getArg(i)));
        }

        return newFact;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        var newFact = cp.newInitialFact();
        var invoke = (Invoke)edge.getCallSite();

        var v = invoke.getLValue();
        if (v != null) {
            var res = edge.getReturnVars().stream().map(returnOut::get)
                .reduce(Value.getUndef(), cp::meetValue);
            newFact.update(v, res);
        }
        return newFact;
    }
}
