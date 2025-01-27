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

package pascal.taie.analysis.dataflow.solver;

import java.util.LinkedList;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        var workList = new LinkedList<Node>();
        for (Node n: cfg) {
            workList.push(n);
        }

        while (!workList.isEmpty()) {
            var cur = workList.pollFirst();
            var in = analysis.newInitialFact();
            var out = result.getOutFact(cur);
            for (var pred: cfg.getPredsOf(cur)) {
                analysis.meetInto(result.getOutFact(pred), in);
            }
            result.setInFact(cur, in);
            if (analysis.transferNode(cur, in, out)) {
                for (var succ: cfg.getSuccsOf(cur)) {
                    workList.push(succ);
                }
            }
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        var workList = new LinkedList<Node>();
        for (Node n: cfg) {
            workList.push(n);
        }

        while (!workList.isEmpty()) {
            var cur = workList.pollFirst();
            var in = result.getInFact(cur);
            var out = analysis.newInitialFact();
            for (var succ: cfg.getSuccsOf(cur)) {
                analysis.meetInto(result.getInFact(succ), out);
            }
            result.setOutFact(cur, out);
            if (analysis.transferNode(cur, in, out)) {
                for (var pred: cfg.getPredsOf(cur)) {
                    workList.push(pred);
                }
            }
        }
    }
}
