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
 
import java.util.Map;
import java.util.stream.Stream;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.BinaryExp;
import pascal.taie.ir.exp.BitwiseExp;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.ShiftExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

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
        // TODO - finish me
        CPFact res = new CPFact();
        for(Var var : cfg.getIR().getParams()) if(canHoldInt(var)) {
            res.update(var, Value.getNAC());
        }   
        return res;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        Stream<Map.Entry<Var, Value>> entries = fact.entries();
        entries.forEach(entry -> {
            // Value v = target.get(entry.getKey());
            // if(v == null) {
            //     target.update(entry.getKey(), entry.getValue());
            // }else if(v.equals(entry.getValue())) {
            //     ; // PASS
            // }else {
            //     target.update(entry.getKey(), Value.getNAC());
            // }
            target.update(entry.getKey(), meetValue(target.get(entry.getKey()), entry.getValue()));
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        Value res;
        if(v1.isNAC()) {
            res = Value.getNAC();
        }else if(v1.isUndef()) {
            res = v2;
        }else if(v1.isConstant() && v2.isConstant() && v1.getConstant() == v2.getConstant()) {
            res = v1;
        }else {
            res = Value.getNAC();
        }

        return res; 
    }

    /**
     * @return whether the in[stmt] is changed
     */
    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact new_in = in.copy();
        CPFact new_out = new CPFact();
        
        if(stmt.getDef().isPresent()) {
            // new_in.remove(stmt.getDef());
            LValue def = stmt.getDef().get();
            if(def instanceof Var var && canHoldInt(var)) {
                new_in.remove(var);
            }

            if(stmt instanceof DefinitionStmt ds && ds.getLValue() instanceof Var l_var) {
                new_out.update(l_var, evaluate(ds.getRValue(), in));
            }
        }

        new_out.copyFrom(new_in);

        return out.copyFrom(new_out);
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
        // TODO - finish me
        Value res = null;
        if(exp instanceof BinaryExp binaryExp) {
            Value v1 = in.get(binaryExp.getOperand1()), v2 = in.get(binaryExp.getOperand2());
            if(v1.isConstant() && v2.isConstant()) {
                int c1 = v1.getConstant(), c2 = v2.getConstant();
                if(binaryExp instanceof ArithmeticExp aexp) {
                    res = switch (aexp.getOperator()) {
                        case ADD -> Value.makeConstant(c1 + c2);
                        case SUB -> Value.makeConstant(c1 - c2);
                        case MUL -> Value.makeConstant(c1 * c2);
                        case DIV -> c2 == 0 ? Value.getUndef() : Value.makeConstant(c1 / c2);
                        case REM -> c2 == 0 ? Value.getUndef() : Value.makeConstant(c1 % c2);
                    };
                }else if(binaryExp instanceof BitwiseExp bexp) {
                    res = switch (bexp.getOperator()) {
                        case OR -> Value.makeConstant(c1 | c2);
                        case AND -> Value.makeConstant(c1 & c2);
                        case XOR -> Value.makeConstant(c1 ^ c2);
                    };
                }else if(binaryExp instanceof ConditionExp cexp) {
                    res = switch (cexp.getOperator()) {
                        case EQ -> Value.makeConstant(c1 == c2 ? 1 : 0);
                        case NE -> Value.makeConstant(c1 != c2 ? 1 : 0);
                        case LT -> Value.makeConstant(c1 < c2 ? 1 : 0);
                        case GT -> Value.makeConstant(c1 > c2 ? 1 : 0);
                        case LE -> Value.makeConstant(c1 <= c2 ? 1 : 0);
                        case GE -> Value.makeConstant(c1 >= c2 ? 1 : 0);
                    };
                }else if(binaryExp instanceof ShiftExp sexp) {
                    res = switch (sexp.getOperator()) {
                        case SHL -> Value.makeConstant(c1 << c2);
                        case SHR -> Value.makeConstant(c1 >> c2);
                        case USHR -> Value.makeConstant(c1 >>> c2);
                    };
                }
            }else if(v1.isNAC() || v2.isNAC()) {
                res = Value.getNAC();
            }else {
                res = Value.getUndef();
            }
        }else if(exp instanceof Var var) {
            res = in.get(var);
        }else if(exp instanceof IntLiteral il) {
            res = Value.makeConstant(il.getValue());
        }else {
            res = Value.getNAC();
        }

        assert(res != null);
        
        return res;
    }
}
