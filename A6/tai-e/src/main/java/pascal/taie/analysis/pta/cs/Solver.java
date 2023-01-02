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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.HashSet;
import java.util.Set;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    private Set<CSMethod> reachableMethods;
    private Set<Stmt> reachableStmts;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        reachableMethods = new HashSet<>();
        reachableStmts = new HashSet<>();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        if (reachableMethods.contains(csMethod)) {
            return;
        }
        reachableMethods.add(csMethod);
        callGraph.addReachableMethod(csMethod);
        var context = csMethod.getContext();
        var method = csMethod.getMethod();
        method.getIR().stmts().forEach(reachableStmts::add);

        method.getIR().stmts().forEach(x -> x.accept(new StmtVisitor<Object>() {
            @Override
            public Object visit(New stmt) {
                var heapContext = contextSelector.selectHeapContext(csMethod, heapModel.getObj(stmt));
                workList.addEntry(csManager.getCSVar(context, stmt.getLValue()), PointsToSetFactory.make(
                        csManager.getCSObj(heapContext, heapModel.getObj(stmt))
                ));
                return null;
            }

            @Override
            public Object visit(Copy stmt) {
                addPFGEdge(
                        csManager.getCSVar(context, stmt.getRValue()),
                        csManager.getCSVar(context, stmt.getLValue())
                );
                return null;
            }

            @Override
            public Object visit(LoadField stmt) {
                if (stmt.isStatic()) {
                    addPFGEdge(csManager.getStaticField(stmt.getFieldRef().resolve()),
                            csManager.getCSVar(context, stmt.getLValue()));
                }
                return null;
            }

            @Override
            public Object visit(StoreField stmt) {
                if (stmt.isStatic()) {
                    addPFGEdge(csManager.getCSVar(context, stmt.getRValue()),
                            csManager.getStaticField(stmt.getFieldRef().resolve()));
                }
                return null;
            }

            @Override
            public Object visit(Invoke stmt) {
                if (stmt.isStatic()) {
                    var method = resolveCallee(null, stmt);
                    addReachable(csManager.getCSMethod(context, method));
                    var newContext = contextSelector.selectContext(
                            csManager.getCSCallSite(context, stmt), method
                    );
                    var argCount = stmt.getInvokeExp().getArgCount();
                    for (int i = 0; i < argCount; i++) {
                        addPFGEdge(csManager.getCSVar(context, stmt.getInvokeExp().getArg(i)),
                                csManager.getCSVar(newContext, method.getIR().getParam(i)));
                    }
                    if (stmt.getLValue() != null) {
                        method.getIR().getReturnVars().forEach(ret -> addPFGEdge(csManager.getCSVar(newContext, ret),
                                csManager.getCSVar(context, stmt.getLValue())));
                    }
                }
                return null;
            }
        }));
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        if (pointerFlowGraph.addEdge(source, target)) {
            if (!source.getPointsToSet().isEmpty()) {
                workList.addEntry(target, source.getPointsToSet());
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while (!workList.isEmpty()) {
            var top = workList.pollEntry();
            var cur = top.pointer();
            var pts = top.pointsToSet();
            var delta = propagate(cur, pts);
            if (cur instanceof CSVar csVar) {
                var v = csVar.getVar();
                var context = csVar.getContext();
                for (var to: delta) {
                    for (var storeField: v.getStoreFields()) {
                        if (reachableStmts.contains(storeField)) {
                            addPFGEdge(csManager.getCSVar(context, storeField.getRValue()),
                                    csManager.getInstanceField(to, storeField.getFieldRef().resolve()));
                        }
                    }
                    for (var loadField: v.getLoadFields()) {
                        if (reachableStmts.contains(loadField)) {
                            addPFGEdge(csManager.getInstanceField(to, loadField.getFieldRef().resolve()),
                                    csManager.getCSVar(context, loadField.getLValue()));
                        }
                    }
                    for (var loadArray: v.getLoadArrays()) {
                        if (reachableStmts.contains(loadArray)) {
                            addPFGEdge(csManager.getArrayIndex(to),
                                    csManager.getCSVar(context, loadArray.getLValue()));
                        }
                    }
                    for (var storeArray: v.getStoreArrays()) {
                        if (reachableStmts.contains(storeArray)) {
                            addPFGEdge(csManager.getCSVar(context, storeArray.getRValue()),
                                    csManager.getArrayIndex(to));
                        }
                    }
                    processCall(csVar, to);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        var delta = PointsToSetFactory.make();
        for (var obj: pointsToSet) {
            if (!pointer.getPointsToSet().contains(obj)) {
                delta.addObject(obj);
            }
        }
        if (!delta.isEmpty()) {
            pointer.getPointsToSet().addAll(delta);
            pointerFlowGraph.getSuccsOf(pointer).forEach(succ -> workList.addEntry(succ, delta));
        }
        return delta;
    }

    private CallKind getCallKind(Invoke i) {
        CallKind kind;
        if (i.isVirtual()) {
            kind = CallKind.VIRTUAL;
        } else if (i.isSpecial()) {
            kind = CallKind.SPECIAL;
        } else if (i.isDynamic()) {
            kind = CallKind.DYNAMIC;
        } else if (i.isStatic()) {
            kind = CallKind.STATIC;
        } else if (i.isInterface()) {
            kind = CallKind.INTERFACE;
        } else {
            kind = CallKind.OTHER;
        }
        return kind;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        for (var invoke: recv.getVar().getInvokes()) {
            if (!reachableStmts.contains(invoke) || invoke.isStatic()) {
                continue;
            }
            var method = resolveCallee(recvObj, invoke);
            if (method.isAbstract()) {
                continue;
            }
            var context = contextSelector.selectContext(
                    csManager.getCSCallSite(recv.getContext(), invoke),
                    recvObj,
                    method
            );
            workList.addEntry(csManager.getCSVar(context, method.getIR().getThis()), PointsToSetFactory.make(recvObj));
            if (callGraph.addEdge(new Edge<>(getCallKind(invoke), csManager.getCSCallSite(recv.getContext(), invoke),
                    csManager.getCSMethod(context, method)))) {
                addReachable(csManager.getCSMethod(context, method));
                int argCount = invoke.getInvokeExp().getArgCount();
                for (int i = 0; i < argCount; i++) {
                    addPFGEdge(csManager.getCSVar(recv.getContext(), invoke.getInvokeExp().getArg(i)),
                            csManager.getCSVar(context, method.getIR().getParam(i)));
                }
                if (invoke.getLValue() != null) {
                    method.getIR().getReturnVars().forEach(ret -> addPFGEdge(csManager.getCSVar(context, ret),
                            csManager.getCSVar(recv.getContext(), invoke.getLValue())));
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
