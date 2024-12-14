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

import java.util.HashSet;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import static pascal.taie.analysis.dataflow.inter.InterConstantPropagation.staticFiledToStore;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.graph.icfg.ICFGEdge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.StoreField;

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

    // private final ConstantPropagation cp;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
        // cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
        // TODO - finish me
        for(Node node : icfg) {
            result.setOutFact(node, analysis.newInitialFact());
            result.setInFact(node, analysis.newInitialFact());
        }
        // icfg.entryMethods().forEach(method -> result.setOutFact(icfg.getEntryOf(method), analysis.newBoundaryFact(icfg.getEntryOf(method))));
        for(Method method : icfg.entryMethods().collect(Collectors.toList())) {
            result.setOutFact(icfg.getEntryOf(method), analysis.newBoundaryFact(icfg.getEntryOf(method)));
        }
    }

    // private void doSolveInMid(Stmt stmt, CPFact in) {
    //     if(stmt instanceof LoadField lf) {
    //         FieldRef fieldRef = lf.getRValue().getFieldRef();
    //         if(lf.isStatic()) {
    //             Value val = Value.getUndef();
    //             for(StoreField sf : staticFiledToStore.getOrDefault(fieldRef, new HashSet<>())) {
    //                 Var var = sf.getRValue();
    //                 val = cp.meetValue(val, in.get(var));
    //             }

    //         }
    //     }
    // }

    private void doSolve() {
        // TODO - finish me
        Set<Node> worklist = new HashSet<>(icfg.getNodes());
        Set<Node> buffer = new HashSet<>();
        while(!worklist.isEmpty()) {
            for(Node node : worklist) {
                Fact new_in = result.getInFact(node);
                for(ICFGEdge<Node> inEdge : icfg.getInEdgesOf(node)) {
                    analysis.meetInto(analysis.transferEdge(inEdge, result.getOutFact(inEdge.getSource())), new_in);
                }
                result.setInFact(node, new_in);

                // if(node.getClass() == Stmt)
                // doSolveInMid((Stmt) node, (CPFact) new_in);
                
                Fact new_out = result.getOutFact(node);
                if(analysis.transferNode(node, new_in, new_out)) {
                    buffer.addAll(icfg.getSuccsOf(node));
                }
                result.setOutFact(node, new_out);
            }
            Set<Node> temp = worklist;
            worklist = buffer;
            buffer = temp;
            buffer.clear();
        }
    }
}
