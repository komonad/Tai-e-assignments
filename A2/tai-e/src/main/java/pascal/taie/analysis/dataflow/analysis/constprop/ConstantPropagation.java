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

package pascal.taie.analysis.dataflow.analysis.constprop;

import java.util.Objects;
import java.util.function.BiFunction;

import org.checkerframework.checker.units.qual.A;
import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.Binary;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.Unary;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        var result = new CPFact();
        for (var v: cfg.getIR().getParams()) {
            if (canHoldInt(v)) {
                result.update(v, Value.getNAC());
            }
        }
        return result;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        for (var key: fact.keySet()) {
            target.update(
                key,
                meetValue(fact.get(key), target.get(key))
            );
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isNAC() || v2.isNAC()) return Value.getNAC();
        if (v1.isUndef()) return v2;
        if (v2.isUndef()) return v1;
        if (v1.getConstant() != v2.getConstant()) return Value.getNAC();
        return v1;
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        var oldOut = out.copy();
        out.copyFrom(in);
        if (stmt instanceof AssignStmt ass && ass.getLValue() instanceof Var v && canHoldInt(v)) {
            var res = evaluate(ass.getRValue(), in);
            out.update(v, res);
        } else if (stmt instanceof DefinitionStmt def && def.getLValue() instanceof Var v && canHoldInt(v)) {
            out.update(v, Value.getNAC());
        }
        return !oldOut.equals(out);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        if (var == null) return false;
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    private static BiFunction<Integer, Integer, Value> getEvaluatorFromOp(BinaryExp.Op op) {
        BiFunction<Integer, Integer, Value> evaluator = (x, y) -> Value.getUndef();
        if (op instanceof ArithmeticExp.Op aop) {
            evaluator = (x, y) ->
                switch (aop) {
                    case ADD -> Value.makeConstant(x + y);
                    case SUB -> Value.makeConstant(x - y);
                    case MUL -> Value.makeConstant(x * y);
                    case DIV -> y == 0 ? Value.getUndef() : Value.makeConstant(x / y);
                    case REM -> y == 0 ? Value.getUndef() : Value.makeConstant(x % y);
                };
        } else if (op instanceof ConditionExp.Op cop) {
            evaluator = (x, y) ->
                switch (cop) {
                    case NE -> Value.makeConstant(x != y ? 1 : 0);
                    case EQ -> Value.makeConstant(x == y ? 1 : 0);
                    case GE -> Value.makeConstant(x >= y ? 1 : 0);
                    case LE -> Value.makeConstant(x <= y ? 1 : 0);
                    case LT -> Value.makeConstant(x <  y ? 1 : 0);
                    case GT -> Value.makeConstant(x >  y ? 1 : 0);
                };
        } else if (op instanceof ShiftExp.Op sop) {
            evaluator = (x, y) ->
                switch (sop) {
                    case SHL  -> Value.makeConstant(x <<  y);
                    case SHR  -> Value.makeConstant(x >>  y);
                    case USHR -> Value.makeConstant(x >>> y);
                };
        } else if (op instanceof BitwiseExp.Op bop) {
            evaluator = (x, y) ->
                switch (bop) {
                    case OR  -> Value.makeConstant(x | y);
                    case AND -> Value.makeConstant(x & y);
                    case XOR -> Value.makeConstant(x ^ y);
                };
        }
        return evaluator;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        if (exp instanceof Var v && canHoldInt(v)) {
            return in.get(v);
        } else if (exp instanceof IntLiteral lit) {
            return Value.makeConstant(lit.getValue());
        } else if (exp instanceof BinaryExp binaryExp) {
            var left = in.get(binaryExp.getOperand1());
            var right = in.get(binaryExp.getOperand2());

            if (right.isConstant() && right.getConstant() == 0 && (
                binaryExp.getOperator() instanceof ArithmeticExp.Op op && (op == ArithmeticExp.Op.DIV || op == ArithmeticExp.Op.REM)
                )) {
                return Value.getUndef();
            }

            if (left.isNAC() || right.isNAC()) return Value.getNAC();
            if (left.isConstant() && right.isConstant()) {
                var op = binaryExp.getOperator();
                var evaluator = getEvaluatorFromOp(op);
                return evaluator.apply(left.getConstant(), right.getConstant());
            }
            return Value.getUndef();
        }
        return Value.getNAC();
    }
}
