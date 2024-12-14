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

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import heros.solver.Pair;
import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JMethod;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    public static Map<Obj, Set<Var>> objToPtr = new HashMap<>();

    // public static Map<Var, Set<Var>> alias = new HashMap<>();

    public static Map<Pair<Obj, FieldRef>, Set<StoreField>> objFiledToStore = new HashMap<>();
    //                   <Base, Filed>

    public static Map<FieldRef, Set<StoreField>> staticFiledToStore = new HashMap<>();

    public static Map<Obj, Set<StoreArray>> arrayToStore = new HashMap<>();

    public static PointerAnalysisResult pta;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    private void getStaticFiledStore(StoreField sf) {
        // When analyzing a load statement of a static field, say x = T.f;, you just need to look up the store statements of the same field (T.f) in the program, and meet the stored values to the LHS variable (x) of the load statement.
        FieldRef fieldRef = sf.getLValue().getFieldRef();
        Set<StoreField> set = staticFiledToStore.getOrDefault(fieldRef, new HashSet<>());
        set.add(sf);
        staticFiledToStore.put(fieldRef, set);
    }

    private void getInstanceFieldStore(StoreField sf) {
        // When analyzing an instance field load, say L, we look up the store statements which modify the aliases of the instance field and meet the stored values to the LHS variable of L as shown below
        if(sf.getFieldAccess() instanceof InstanceFieldAccess ifa) {
            pta.getPointsToSet(ifa.getBase()).forEach(obj -> {
                Pair<Obj, FieldRef> objField = new Pair<>(obj, ifa.getFieldRef());
                Set<StoreField> set = objFiledToStore.getOrDefault(objField, new HashSet<>());
                set.add(sf);
                objFiledToStore.put(objField, set);
            });
        }
    }
    
    private void getArrayStore(StoreArray sa) {
        ArrayAccess aa = sa.getArrayAccess();
        pta.getPointsToSet(aa.getBase()).forEach(obj -> {
            Set<StoreArray> set = arrayToStore.getOrDefault(obj, new HashSet<>());
            set.add(sa);
            arrayToStore.put(obj, set);
        });
    }

    private void doStore() {
        icfg.getNodes().forEach(stmt -> {
            if(stmt instanceof StoreField sf) {
                if(sf.isStatic()) {
                    getStaticFiledStore(sf);
                }else {
                    getInstanceFieldStore(sf);
                }
            }else if(stmt instanceof StoreArray sa) {
                getArrayStore(sa);
            }
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
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

    /**
     * @return alias list map, one's alias can be itself.
     */
    private void getAliases() {
        pta.getCSVars().forEach(csVar -> {
            csVar.getPointsToSet().forEach(csObj -> {
                Set<Var> tar = objToPtr.getOrDefault(csObj.getObject(), new HashSet<>());
                tar.add(csVar.getVar());
                objToPtr.put(csObj.getObject(), tar);
            });
        });

        // objToPtr.forEach((obj, set) -> {
        //     set.forEach(i -> {
        //         set.forEach(j -> {
        //             alias.getOrDefault(i, new HashSet<>()).add(j);
        //             alias.put(...)
        //             alias.getOrDefault(j, new HashSet<>()).add(i);
        //             alias.put(...)
        //         });
        //     });
        // });
    }

    // private void doStaticFiledStore() {
    //     icfg.getNodes().forEach(stmt -> {
    //         if(stmt instanceof StoreField sf && sf.isStatic()) {
    //             Set<StoreField> set = staticFiledToVal.getOrDefault(sf.getLValue().getFieldRef().getDeclaringClass(), new HashSet<>());
    //             set.add()
    //         }
    //     });
    // }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        pta = World.get().getResult(ptaId);
        // You can do initialization work here
        getAliases();
        doStore();
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }


    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        return out.copyFrom(in);
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        return cp.transferNode(stmt, in, out);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        Stmt src = edge.getSource(), tar = edge.getTarget();
        IR ir = icfg.getContainingMethodOf(tar).getIR();
        CPFact calleeIn = new CPFact();
        if(src instanceof DefinitionStmt dstmt) {
            RValue rv = dstmt.getRValue();
            if(rv instanceof InvokeExp iexp) {
                int argc = iexp.getArgs().size();
                for(int i = 0; i < argc; i++) {
                    calleeIn.update(ir.getParam(i), callSiteOut.get(iexp.getArg(i)));
                }
            }
        }

        return calleeIn;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        CPFact callerReturnIn = new CPFact();
        Stmt callSite = edge.getCallSite();
        if(callSite.getDef().isPresent()) {
            LValue lv = callSite.getDef().get();
            if(lv instanceof Var lvar) {
                Value returnValue = Value.getUndef();
                for(Var var : edge.getReturnVars()) {
                    returnValue = cp.meetValue(returnOut.get(var), returnValue);
                }
                if(!returnValue.isUndef()) {
                    callerReturnIn.update(lvar, returnValue);
                }
            }
        }

        return callerReturnIn;
    }
}