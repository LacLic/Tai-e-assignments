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

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedList;
import java.util.Map;
import java.util.Queue;
import java.util.Set;
import java.util.TreeSet;
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
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

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

        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode
        Queue<Stmt> q = new LinkedList<>();
        q.add(cfg.getEntry());
        ArrayList<Boolean> isVisited = new ArrayList<>(Collections.nCopies(cfg.getNodes().size(), false));
        while(!q.isEmpty()) {
            Stmt stmt = q.poll();
            isVisited.set(stmt.getIndex(), true);
            if(stmt instanceof If ifs) {
                Value val = ConstantPropagation.evaluate(ifs.getCondition(), constants.getInFact(ifs));
                for(Edge<Stmt> edge : cfg.getOutEdgesOf(ifs)) {
                    if(edge.getKind() == Edge.Kind.IF_TRUE && (val.isConstant() && val.getConstant() == 1 || val.isNAC())) {
                        q.add(edge.getTarget());
                    }
                    if(edge.getKind() == Edge.Kind.IF_FALSE && (val.isConstant() && val.getConstant() == 0 || val.isNAC())) {
                        q.add(edge.getTarget());
                    }
                }
            }else if(stmt instanceof SwitchStmt swt) {
                Value val = ConstantPropagation.evaluate(swt.getVar(), constants.getInFact(swt));
                if(val.isNAC()) {
                    for(Edge<Stmt> edge : cfg.getOutEdgesOf(swt)) {
                        q.add(edge.getTarget());
                    }
                }else { assert(val.isConstant());
                    boolean isDefault = true;
                    for(Edge<Stmt> edge : cfg.getOutEdgesOf(swt)) {
                        if(val.getConstant() == edge.getCaseValue()) {
                            isDefault = false;
                            q.add(edge.getTarget());
                        }
                    }
                    if(isDefault) {
                        q.add(swt.getDefaultTarget());
                    }
                }
            }else if(stmt instanceof DefinitionStmt dfn) {
                if(hasNoSideEffect(dfn.getRValue()) && dfn instanceof AssignStmt asn) {
                    if(asn.getLValue() instanceof Var lvar) {
                        if(!liveVars.getOutFact(asn).contains(lvar)) {
                            deadCode.add(asn);
                        }
                    }
                }
                for(Edge<Stmt> edge : cfg.getOutEdgesOf(dfn)) {
                    q.add(edge.getTarget());
                }
            }else {
                for(Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
                    q.add(edge.getTarget());
                }
            }
        }
        for(Stmt stmt : cfg.getNodes()) if(!isVisited.get(stmt.getIndex())) {
            deadCode.add(stmt);
        }

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
