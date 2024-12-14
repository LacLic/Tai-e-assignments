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

import java.util.HashSet;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import static pascal.taie.analysis.dataflow.inter.InterConstantPropagation.arrayToStore;
import static pascal.taie.analysis.dataflow.inter.InterConstantPropagation.objFiledToStore;
import static pascal.taie.analysis.dataflow.inter.InterConstantPropagation.pta;
import static pascal.taie.analysis.dataflow.inter.InterConstantPropagation.staticFiledToStore;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.BinaryExp;
import pascal.taie.ir.exp.BitwiseExp;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.ShiftExp;
import pascal.taie.ir.exp.StaticFieldAccess;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Pair;

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
        fact.entries().forEach(entry -> {
            target.update(entry.getKey(), meetValue(target.get(entry.getKey()), entry.getValue()));
        });
    }

    /**
     * Meets two Values.
     */
    public static Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        Value res;
        if(v1.isNAC() || v2.isNAC()) {
            res = Value.getNAC();
        }else if(v1.isConstant() && v2.isConstant()) {
            if(v1.getConstant() == v2.getConstant()) {
                res = Value.makeConstant(v1.getConstant());
            }else {
                res = Value.getNAC();
            }
        }else if(v1.isConstant() && v2.isUndef()) {
            res = Value.makeConstant(v1.getConstant());
        }else if(v1.isUndef() && v2.isConstant()) {
            res = Value.makeConstant(v2.getConstant());
        }else /* v1,v2 both Undef */ {
            res = Value.getUndef();
        }

        return res; 
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact new_in = in.copy();
        CPFact new_out = new CPFact();
        
        if(stmt instanceof DefinitionStmt ds && ds.getLValue() instanceof Var var && canHoldInt(var)) {
            new_in.remove(var);
            new_out.update(var, evaluate(ds.getRValue(), in));
        }else if(stmt instanceof LoadField lf && canHoldInt(lf.getLValue())) {
            Var var = lf.getLValue();
            new_in.remove(var);
            FieldAccess fieldAccess = lf.getRValue();
            new_out.update(var, evaluate(fieldAccess, in));
        }else if(stmt instanceof LoadArray la && canHoldInt(la.getLValue())) {
            Var var = la.getLValue();
            new_in.remove(var);
            ArrayAccess arrayAccess = la.getRValue();
            new_out.update(var, evaluate(arrayAccess, in));
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
            if(exp instanceof ArithmeticExp aexp && (aexp.getOperator() == ArithmeticExp.Op.DIV || aexp.getOperator() == ArithmeticExp.Op.REM) && v2.isConstant() && v2.getConstant() == 0) {
                res = Value.getUndef();
            }else if(v1.isConstant() && v2.isConstant()) {
                int c1 = v1.getConstant(), c2 = v2.getConstant();
                if(binaryExp instanceof ArithmeticExp aexp) {
                    res = switch (aexp.getOperator()) {
                        case ADD -> Value.makeConstant(c1 + c2);
                        case SUB -> Value.makeConstant(c1 - c2);
                        case MUL -> Value.makeConstant(c1 * c2);
                        case DIV -> Value.makeConstant(c1 / c2);
                        case REM -> Value.makeConstant(c1 % c2);
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
        }else if(exp instanceof StaticFieldAccess sa) {
            res = Value.getUndef();
            for(StoreField sf : staticFiledToStore.getOrDefault(sa.getFieldRef(), new HashSet<>())) {
                Var var = sf.getRValue();
                res = meetValue(res, in.get(var));
            }
        }else if(exp instanceof InstanceFieldAccess ifa) {
            res = Value.getUndef();
            for(Obj obj : pta.getPointsToSet(ifa.getBase())) {
                Pair<Obj, FieldRef> objField = new Pair<>(obj, ifa.getFieldRef());
                for(StoreField sf : objFiledToStore.getOrDefault(objField, new HashSet<>())) {
                    Var var = sf.getRValue();
                    res = meetValue(res, in.get(var));
                }
            }
        }else if(exp instanceof ArrayAccess aa) {
            res = Value.getUndef(); // now_load_var_value
            for(Obj obj : pta.getPointsToSet(aa.getBase())) {
                for(StoreArray sf : arrayToStore.getOrDefault(obj, new HashSet<>())) {
                    Var prev_store_var = sf.getRValue();
                    Var prev_store_index = sf.getLValue().getIndex();
                    Var now_load_index = aa.getIndex();
                    if(in.get(prev_store_index).isNAC()
                    || in.get(now_load_index).isNAC()
                    || in.get(prev_store_index).getConstant() == in.get(now_load_index).getConstant()) {
                        res = meetValue(res, in.get(prev_store_var));
                    }
                }
            }
        }else {
            res = Value.getNAC();
        }

        assert(res != null);
        
        return res;
    }
}
