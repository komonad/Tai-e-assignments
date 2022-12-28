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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private Set<JMethod> reachableMethods;

    private Set<Stmt> reachableStmts;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        hierarchy = World.get().getClassHierarchy();
        reachableMethods = new HashSet<>();
        reachableStmts = new HashSet<>();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        if (reachableMethods.contains(method)) {
            return;
        }
        reachableMethods.add(method);
        callGraph.addReachableMethod(method);
        method.getIR().stmts().forEach(reachableStmts::add);
        method.getIR().stmts().forEach(x -> x.accept(new StmtVisitor<Void>() {
            @Override
            public Void visit(New stmt) {
                workList.addEntry(pointerFlowGraph.getVarPtr(stmt.getLValue()), new PointsToSet(heapModel.getObj(stmt)));
                return null;
            }

            @Override
            public Void visit(Copy stmt) {
                addPFGEdge(
                        pointerFlowGraph.getVarPtr(stmt.getRValue()),
                        pointerFlowGraph.getVarPtr(stmt.getLValue()));
                return null;
            }

            @Override
            public Void visit(LoadField stmt) {
                if (stmt.isStatic()) {
                    addPFGEdge(pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve()),
                            pointerFlowGraph.getVarPtr(stmt.getLValue()));
                }
                return null;
            }

            @Override
            public Void visit(StoreField stmt) {
                if (stmt.isStatic()) {
                    addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue()),
                            pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve()));
                }
                return null;
            }

            @Override
            public Void visit(Invoke stmt) {
                if (stmt.isStatic()) {
                    var method = resolveCallee(null, stmt);
                    addReachable(method);
                    var argCount = stmt.getInvokeExp().getArgCount();
                    for (int i = 0; i < argCount; i++) {
                        addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getInvokeExp().getArg(i)),
                                pointerFlowGraph.getVarPtr(method.getIR().getParam(i)));
                    }
                    if (stmt.getLValue() != null) {
                        method.getIR().getReturnVars().forEach(ret ->
                                addPFGEdge(pointerFlowGraph.getVarPtr(ret),
                                        pointerFlowGraph.getVarPtr(stmt.getLValue())));
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
            var cur = workList.pollEntry();
            var ptr = cur.pointer();
            var delta = propagate(ptr, cur.pointsToSet());
            if (ptr instanceof VarPtr vp) { // v -> { Delta... }
                var v = vp.getVar();
                for (var storeField: v.getStoreFields()) { // v.f = y
                    if (reachableStmts.contains(storeField)) {
                        delta.forEach(x -> addPFGEdge(pointerFlowGraph.getVarPtr(storeField.getRValue()),
                                pointerFlowGraph.getInstanceField(x, storeField.getFieldRef().resolve())));
                    }
                }
                for (var loadField: v.getLoadFields()) { // y = v.f
                    if (reachableStmts.contains(loadField)) {
                        delta.forEach(x -> addPFGEdge(pointerFlowGraph.getInstanceField(x, loadField.getFieldRef().resolve()),
                                pointerFlowGraph.getVarPtr(loadField.getLValue())));
                    }
                }
                for (var storeArray: v.getStoreArrays()) { // v[*] = y
                    if (reachableStmts.contains(storeArray)) {
                        delta.forEach(x -> addPFGEdge(pointerFlowGraph.getVarPtr(storeArray.getRValue()),
                                pointerFlowGraph.getArrayIndex(x)));
                    }
                }
                for (var loadArray: v.getLoadArrays()) { // y = v[*]
                    if (reachableStmts.contains(loadArray)) {
                        delta.forEach(x -> addPFGEdge(pointerFlowGraph.getArrayIndex(x),
                                pointerFlowGraph.getVarPtr(loadArray.getLValue())));
                    }
                }
                delta.forEach(o -> processCall(v, o));
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        var delta = new PointsToSet();
        for (var v: pointsToSet) {
            if (!pointer.getPointsToSet().contains(v)) {
                delta.addObject(v);
            }
        }

        if (!delta.isEmpty()) {
            pointsToSet.forEach(pointer.getPointsToSet()::addObject);
            for (var to: pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(to, delta);
            }
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
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        for (var invoke: var.getInvokes()) {
            if (reachableStmts.contains(invoke) && !invoke.isStatic()) {
                var method = resolveCallee(recv, invoke);
                workList.addEntry(pointerFlowGraph.getVarPtr(method.getIR().getThis()), new PointsToSet(recv));
                if (callGraph.addEdge(new Edge<>(getCallKind(invoke), invoke, method))) {
                    addReachable(method);
                    int paramCount = invoke.getInvokeExp().getArgCount();
                    for (int i = 0; i < paramCount; i++) {
                        addPFGEdge(
                                pointerFlowGraph.getVarPtr(invoke.getInvokeExp().getArg(i)),
                                pointerFlowGraph.getVarPtr(method.getIR().getParam(i))
                        );
                    }
                    if (invoke.getLValue() != null) {
                        method.getIR().getReturnVars().forEach(ret -> addPFGEdge(
                                pointerFlowGraph.getVarPtr(ret),
                                pointerFlowGraph.getVarPtr(invoke.getLValue())
                        ));
                    }
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
