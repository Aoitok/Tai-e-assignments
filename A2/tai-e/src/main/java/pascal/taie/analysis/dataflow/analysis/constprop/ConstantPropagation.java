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

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.BinaryExp;
import pascal.taie.ir.exp.BitwiseExp;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.ShiftExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
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
        CPFact result = new CPFact();
        IR ir = cfg.getIR();
        for (Var var : ir.getParams()) {
            if (canHoldInt(var)) {
                result.update(var, Value.getNAC());
            }
        }
        return result;
    }

    @Override
    public CPFact newInitialFact() {
        CPFact result = new CPFact();
        return result;
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        fact.forEach((var, value) -> target.update(var, meetValue(value, target.get(var))));
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        Value result = Value.getNAC();
        if (!v1.isNAC() && !v2.isNAC()) {
            if (v1.isUndef()) {
                result = v2;
            } else if (v2.isUndef()) {
                result = v1;
            } else if (v1.getConstant() == v2.getConstant()) {
                result = v1;
            }
        }
        return result;
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        CPFact result = in.copy();
        if (stmt instanceof DefinitionStmt defStmt) {
            if (defStmt.getDef().isPresent() && defStmt.getDef().get() instanceof Var var && canHoldInt(var)) {
                result.update(var, evaluate(defStmt.getRValue(), result));
            }
        }
        return out.copyFrom(result);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
                default:
                    break;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        if (exp instanceof Var var)
            return in.get(var);
        if (exp instanceof IntLiteral intLiteral)
            return Value.makeConstant(intLiteral.getValue());
        if (!(exp instanceof BinaryExp))
            return Value.getNAC();
        BinaryExp binaryExp = (BinaryExp) exp;
        Value v1 = in.get(binaryExp.getOperand1());
        Value v2 = in.get(binaryExp.getOperand2());
        if (v1.isUndef() || v2.isUndef())
            return Value.getUndef();
        if (v2.isConstant() && v2.getConstant() == 0
                && binaryExp instanceof ArithmeticExp arithmeticExp
                && (arithmeticExp.getOperator() == ArithmeticExp.Op.DIV
                        || arithmeticExp.getOperator() == ArithmeticExp.Op.REM))
            return Value.getUndef();
        if (v1.isNAC() || v2.isNAC())
            return Value.getNAC();
        int c1 = v1.getConstant();
        int c2 = v2.getConstant();
        if (exp instanceof ArithmeticExp arithmeticExp) {
            switch (arithmeticExp.getOperator()) {
                case ADD:
                    return Value.makeConstant(c1 + c2);
                case SUB:
                    return Value.makeConstant(c1 - c2);
                case MUL:
                    return Value.makeConstant(c1 * c2);
                case DIV:
                    return Value.makeConstant(c1 / c2);
                case REM:
                    return Value.makeConstant(c1 % c2);
            }
        }
        if (exp instanceof BitwiseExp bitwiseExp) {
            switch (bitwiseExp.getOperator()) {
                case OR:
                    return Value.makeConstant(c1 | c2);
                case AND:
                    return Value.makeConstant(c1 & c2);
                case XOR:
                    return Value.makeConstant(c1 ^ c2);
            }
        }
        if (exp instanceof ConditionExp conditionExp) {
            switch (conditionExp.getOperator()) {
                case EQ:
                    return Value.makeConstant(c1 == c2 ? 1 : 0);
                case NE:
                    return Value.makeConstant(c1 != c2 ? 1 : 0);
                case LT:
                    return Value.makeConstant(c1 < c2 ? 1 : 0);
                case GT:
                    return Value.makeConstant(c1 > c2 ? 1 : 0);
                case LE:
                    return Value.makeConstant(c1 <= c2 ? 1 : 0);
                case GE:
                    return Value.makeConstant(c1 >= c2 ? 1 : 0);
            }
        }
        if (exp instanceof ShiftExp shiftExp) {
            switch (shiftExp.getOperator()) {
                case SHL:
                    return Value.makeConstant(c1 << c2);
                case SHR:
                    return Value.makeConstant(c1 >> c2);
                case USHR:
                    return Value.makeConstant(c1 >>> c2);
            }
        }
        return Value.getUndef();
    }

}
