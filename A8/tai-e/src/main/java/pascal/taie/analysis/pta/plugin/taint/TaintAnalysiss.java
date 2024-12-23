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

package pascal.taie.analysis.pta.plugin.taint;

import java.util.Set;
import java.util.TreeSet;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    // TODO - finish me

    /**
     * We define another input of taint analysis, called TaintI'ran fers, which is a set of four-element tuples, denoted
     * as (m, from, to, u), where m indicates the method that triggers taint transfer, from the from variable to the to
     * variable, and u is the type of the transferred taint object (pointed to by to). Specifically,
     * m is a signature of the method that triggers taint transfer, and
     * from is either an integer value (starting from 0) when it represents an argument, or the string "base" when it
     * represents a base variable, and
     * to is either the string "base" when it represents a base variable, or the string "result" when it represents an LHS
     * variable of the call site, and
     * u is the type of the transferred taint object. As a taint transfer may change the type of the taint object (e.g.
     * StringBuilder.tostring() transfers a taint object of type Stringbuilder to a taint object of type
     * String), then we need u to tell the taint analysis what the type of the transferred taint object is. lt would be
     * particularly useful when the type of the transferred object (pointed to by to) differs from the type of the taint
     * object pointed to by from.
     */
    public void taintTransfers(JMethod callee, CSVar base) {

    }


    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.
        result.getCSCallGraph().reachableMethods().forEach(
            csCallee -> result.getCSCallGraph().getCallersOf(csCallee).forEach(
                csCaller -> {
                    JMethod callee = csCallee.getMethod();
                    Invoke caller = csCaller.getCallSite();
                    int n = caller.getRValue().getArgCount();
                    for(int i = 0; i < n; i++) {
                        Var arg = caller.getRValue().getArg(i);
                        Sink sink = new Sink(callee, i);
                        if(config.getSinks().contains(sink)) {
                            for(Obj obj : result.getPointsToSet(arg)) {
                                if(manager.isTaint(obj)) {
                                    taintFlows.add(
                                        new TaintFlow(
                                            manager.getSourceCall(obj),
                                            caller,
                                            i
                                        )
                                    );
                                }
                            }
                        }
                    }
            })
        );
        return taintFlows;
    }
}
