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

package pascal.taie.analysis.pta.ci;

import java.util.Set;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    private Set<JMethod> isVisited;

    private Set<Stmt> stmts;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        if(!isVisited.contains(method)) {
            isVisited.add(method);
            // for(Stmt stmt : method.getIR().getStmts()) {
            //     if(stmt instanceof Invoke ivk) {
            //         if(ivk.isStatic()) {
                        
            //         }
            //     }else if(stmt instanceof New nStmt) {
            //         Pointer ptr = pointerFlowGraph.getVarPtr(nStmt.getLValue());
            //         workList.addEntry(ptr, ptr.getPointsToSet());
            //     }else if(stmt instanceof Copy cp) {
            //         addPFGEdge(
            //             pointerFlowGraph.getVarPtr(cp.getLValue()),
            //             pointerFlowGraph.getVarPtr(cp.getRValue())
            //         );
            //     }
            // }
            method.getIR().getStmts().forEach((stmt) -> {
                stmt.accept(stmtProcessor);
            });
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        @Override
        public Void visit(Invoke ivk) {
            if(ivk.isStatic()) {
                JMethod tar = resolveCallee(null, ivk);
                if(callGraph.addEdge(new Edge<>(CallKind.STATIC, ivk, tar))) {
                    addReachable(tar);
                    int argc = tar.getParamCount();
                    assert argc == ivk.getRValue().getArgCount();
                    for(int i = 0; i < argc; i++) {
                        addPFGEdge(
                            pointerFlowGraph.getVarPtr(ivk.getRValue().getArg(i)),
                            pointerFlowGraph.getVarPtr(tar.getIR().getParam(i))
                        );
                    }
                    tar.getIR().getReturnVars().forEach(retVar ->
                        addPFGEdge(
                            pointerFlowGraph.getVarPtr(retVar),
                            pointerFlowGraph.getVarPtr(ivk.getLValue())
                        )
                    );
                    
                }
            }
            return visitDefault(ivk);
        }

        @Override
        public Void visit(New nw) {
            Pointer ptr = pointerFlowGraph.getVarPtr(nw.getLValue());
            workList.addEntry(ptr, new PointsToSet(heapModel.getObj(nw)));

            return visitDefault(nw);
        }

        @Override
        public Void visit(Copy cp) {
            addPFGEdge(
                pointerFlowGraph.getVarPtr(cp.getLValue()),
                pointerFlowGraph.getVarPtr(cp.getRValue())
            );

            return visitDefault(cp);
        }

        @Override
        public Void visit(LoadField ld) {
            if(ld.isStatic()) {
                addPFGEdge(
                    pointerFlowGraph.getStaticField(ld.getFieldRef().resolve()),
                    pointerFlowGraph.getVarPtr(ld.getLValue())
                );
            }

            return visitDefault(ld);
        }

        @Override
        public Void visit(StoreField st) {
            if(st.isStatic()) {
                addPFGEdge(
                    pointerFlowGraph.getVarPtr(st.getRValue()),
                    pointerFlowGraph.getStaticField(st.getFieldRef().resolve())
                );
            }
            
            return visitDefault(st);
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if(pointerFlowGraph.addEdge(source, target)) {
            PointsToSet pts = source.getPointsToSet();
            if(!pts.isEmpty()) {
                workList.addEntry(target, pts);
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while(!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer ptr = entry.pointer();
            PointsToSet pts = entry.pointsToSet();
            PointsToSet delta = new PointsToSet();
            pts.objects()
                    .filter(obj -> !ptr.getPointsToSet().contains(obj))
                    .forEach(obj -> delta.addObject(obj));
            propagate(ptr, pts);
            if(ptr instanceof VarPtr varPtr) {
                delta.objects().forEach(obj -> {
                    varPtr.getVar().getStoreFields().forEach(field -> {
                        addPFGEdge(
                            pointerFlowGraph.getVarPtr(field.getRValue()),
                            pointerFlowGraph.getInstanceField(obj, field.getFieldRef().resolve())
                        );
                    });

                    varPtr.getVar().getLoadFields().forEach(field -> {
                        addPFGEdge(
                            pointerFlowGraph.getInstanceField(obj, field.getFieldRef().resolve()),
                            pointerFlowGraph.getVarPtr(field.getLValue())
                        );
                    });

                    varPtr.getVar().getStoreArrays().forEach(field -> {
                        addPFGEdge(
                            pointerFlowGraph.getVarPtr(field.getRValue()),
                            pointerFlowGraph.getArrayIndex(obj)
                        );
                    });

                    varPtr.getVar().getLoadArrays().forEach(field -> {
                        addPFGEdge(
                            pointerFlowGraph.getArrayIndex(obj),
                            pointerFlowGraph.getVarPtr(field.getLValue())
                        );
                    });

                    processCall(varPtr.getVar(), obj);
                });
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        if(!pointsToSet.isEmpty()) {
            PointsToSet ptn = pointer.getPointsToSet();
            pointsToSet.forEach(obj -> {
                ptn.addObject(obj);
            });

            pointerFlowGraph.getSuccsOf(pointer).forEach(to -> {
                workList.addEntry(to, pointsToSet);
            });
        }
        return pointsToSet;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        var.getInvokes().forEach(invoke -> {
            JMethod method = resolveCallee(recv, invoke);
            workList.addEntry(
                pointerFlowGraph.getVarPtr(method.getIR().getThis()),
                new PointsToSet(recv)
            );

            CallKind callKind = null;
            if(invoke.isSpecial()) callKind = CallKind.SPECIAL;
            else if(invoke.isVirtual()) callKind = CallKind.VIRTUAL;
            else if(invoke.isInterface()) callKind = CallKind.INTERFACE;

            if(callGraph.addEdge(new Edge<>(callKind, invoke, method))) {
                addReachable(method);
                int argc = method.getParamCount();
                assert argc == invoke.getRValue().getArgCount();
                for(int i = 0; i < argc; i++) {
                    addPFGEdge(
                        pointerFlowGraph.getVarPtr(invoke.getRValue().getArg(i)),
                        pointerFlowGraph.getVarPtr(method.getIR().getParam(i))
                    );
                }
                method.getIR().getReturnVars().forEach(retVar -> {
                    addPFGEdge(
                        pointerFlowGraph.getVarPtr(retVar),
                        pointerFlowGraph.getVarPtr(invoke.getLValue())
                    );
                });
            }
        });
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
