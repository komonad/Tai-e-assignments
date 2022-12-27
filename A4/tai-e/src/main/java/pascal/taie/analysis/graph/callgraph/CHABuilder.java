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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);

        var reachableMethods = new HashSet<JMethod>();
        var workList = new LinkedList<JMethod>();
        workList.push(entry);

        while (!workList.isEmpty()) {
            var cur = workList.pollFirst();
            if (reachableMethods.contains(cur)) continue;
            reachableMethods.add(cur);
            callGraph.addReachableMethod(cur);
            if (cur.isAbstract()) continue;
            cur.getIR().getStmts().stream().filter(x -> x instanceof Invoke)
                    .forEach(x -> {
                        var i = (Invoke) x;
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
                        var targets = resolve(i);
                        for (var target: targets) {
                            callGraph.addEdge(new Edge<>(kind, i, target));
                            workList.add(target);
                        }
                    });
        }

        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        var methodRef = callSite.getMethodRef();
        if (callSite.isStatic()) {
            var klass = methodRef.getDeclaringClass();
            if (klass == null) {
                return Set.of();
            }
            var method = klass.getDeclaredMethod(methodRef.getSubsignature());
            if (method != null) {
                return Set.of(method);
            } else {
                return Set.of();
            }
        }
        if (callSite.isSpecial()) {
            var klass = methodRef.getDeclaringClass();
            return Set.of(dispatch(klass, methodRef.getSubsignature()));
        }
        if (callSite.isVirtual() || callSite.isInterface()) {
            var declClass = methodRef.getDeclaringClass();
            var sig = methodRef.getSubsignature();
            var res = new HashSet<JMethod>();

            var q = new LinkedList<JClass>();
            q.push(declClass);

            while (!q.isEmpty()) {
                var cur = q.pollFirst();
                var method = dispatch(cur, sig);
                if (method != null) {
                    res.add(method);
                }
                q.addAll(hierarchy.getDirectSubclassesOf(cur));
                q.addAll(hierarchy.getDirectImplementorsOf(cur));
                q.addAll(hierarchy.getDirectSubinterfacesOf(cur));
            }
            return res;
        }
        return Set.of();
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        if (jclass == null || subsignature == null) return null;
        var res = jclass.getDeclaredMethod(subsignature);
        if (res != null && !res.isAbstract()) {
            return res;
        }
        return dispatch(jclass.getSuperClass(), subsignature);
    }
}
