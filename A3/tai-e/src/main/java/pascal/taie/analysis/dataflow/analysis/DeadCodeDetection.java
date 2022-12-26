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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.CastExp;
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.NewExp;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.*;
import java.util.function.Consumer;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // Your task is to recognize dead code in ir and add it to deadCode

        // 1. Control flow unreachable statements
        Set<Stmt> reachableStmts = new TreeSet<>(Comparator.comparing(Stmt::getIndex));

        var q = new LinkedList<Stmt>();
        q.push(cfg.getEntry());

        Consumer<Stmt> push = (x) -> {
            if (!reachableStmts.contains(x)) {
                q.push(x);
            }
        };

        while (!q.isEmpty()) {
            var cur = q.pollFirst();
            if (reachableStmts.contains(cur)) continue;
            reachableStmts.add(cur);
            if (cur instanceof If ifStmt) {
                var res = ConstantPropagation.evaluate(ifStmt.getCondition(), constants.getOutFact(cur));
                if (res.isConstant() && res.getConstant() == 1) {
                    cfg.getOutEdgesOf(cur).stream().filter(x -> x.getKind() == Edge.Kind.IF_TRUE)
                            .forEach(x -> push.accept(x.getTarget()));
                } else if (res.isConstant() && res.getConstant() == 0) {
                    cfg.getOutEdgesOf(cur).stream().filter(x -> x.getKind() == Edge.Kind.IF_FALSE)
                            .forEach(x -> push.accept(x.getTarget()));
                } else {
                    for (var out: cfg.getSuccsOf(cur)) {
                        push.accept(out);
                    }
                }
            } else if (cur instanceof SwitchStmt switchStmt) {
                var res = ConstantPropagation.evaluate(switchStmt.getVar(), constants.getOutFact(cur));
                if (res.isConstant()) {
                    var value = res.getConstant();
                    var casePair = switchStmt.getCaseTargets().stream()
                            .filter(x -> x.first() == value).findFirst();
                    if (casePair.isPresent()) {
                        push.accept(casePair.get().second());
                    } else {
                        push.accept(switchStmt.getDefaultTarget());
                    }
                    continue;
                }
                for (var out: cfg.getSuccsOf(cur)) {
                    push.accept(out);
                }
            } else {
                for (var out: cfg.getSuccsOf(cur)) {
                    push.accept(out);
                }
            }
        }

        for (var stmt: cfg.getNodes()) {
            if (!reachableStmts.contains(stmt)) {
                deadCode.add(stmt);
            }
        }

        // 2. Useless assignments

        for (var stmt: cfg.getNodes()) {
            if (stmt instanceof AssignStmt ass && ass.getLValue() instanceof Var v) {
                if (!liveVars.getOutFact(stmt).contains(v) && hasNoSideEffect(ass.getRValue())) {
                    deadCode.add(stmt);
                }
            }
        }

        deadCode.remove(cfg.getExit());

        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
