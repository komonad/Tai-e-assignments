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

import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.util.collection.SetQueue;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        assert analysis.isForward(); // TODO: maybe we should support backward analysis?
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
        for (var node: icfg.getNodes()) {
            result.setInFact(node, analysis.newInitialFact());
            result.setOutFact(node, analysis.newInitialFact());
        }
        icfg.entryMethods().forEach(x -> {
            var node = icfg.getEntryOf(x);
            result.setInFact(node, analysis.newBoundaryFact(node));
            result.setOutFact(node, analysis.newBoundaryFact(node));
        });
    }

    public void addAll() {
        icfg.forEach(x -> {
            if (!workList.contains(x)) workList.add(x);
        });
    }

    private void doSolve() {
        workList = new LinkedList<>();
        icfg.forEach(workList::add);

        while (!workList.isEmpty()) {
            var cur = workList.poll();
            var in = analysis.newInitialFact();
            var out = result.getOutFact(cur);
            for (var inEdge: icfg.getInEdgesOf(cur)) {
                var newResult = analysis.transferEdge(inEdge, result.getOutFact(inEdge.getSource()));
                analysis.meetInto(newResult, in);
            }
            result.setInFact(cur, in);
            if (analysis.transferNode(cur, in, out)) {
                workList.addAll(icfg.getSuccsOf(cur));
            } else {
                int a = 123;
            }
        }
    }
}
