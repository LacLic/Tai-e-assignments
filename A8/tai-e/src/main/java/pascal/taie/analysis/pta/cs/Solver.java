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

package pascal.taie.analysis.pta.cs;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;

import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysiss;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

public class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private TaintAnalysiss taintAnalysis;

    private PointerAnalysisResult result;

    private Map<CSVar, Set<Invoke>> taintInMethodArg;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
        this.taintInMethodArg = new HashMap<>();
    }

    public AnalysisOptions getOptions() {
        return options;
    }

    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    public CSManager getCSManager() {
        return csManager;
    }

    void solve() {
        initialize();
        analyze();
        taintAnalysis.onFinish();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        taintAnalysis = new TaintAnalysiss(this);
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        if(!callGraph.contains(csMethod)) {
            callGraph.addReachableMethod(csMethod);
            csMethod.getMethod().getIR().getStmts().forEach((stmt) -> {
                stmt.accept(new StmtProcessor(csMethod));
            });
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        @Override
        public Void visit(Invoke ivk) {
            if(ivk.isStatic()) {
                CSCallSite csCallSite = csManager.getCSCallSite(context, ivk);
                JMethod callee = resolveCallee(null, ivk);
                Context ct = contextSelector.selectContext(csCallSite, callee);
                doProcessCall(
                    csCallSite,
                    csManager.getCSMethod(ct, callee),
                    CallKind.STATIC
                );
            }

            ivk.getInvokeExp().getArgs().forEach(arg -> {
                CSVar var = csManager.getCSVar(context, arg);
                Set<Invoke> invokes = taintInMethodArg.getOrDefault(var, new HashSet<>());
                invokes.add(ivk);
                taintInMethodArg.put(var, invokes);
            });

            return visitDefault(ivk);
        }

        @Override
        public Void visit(New nw) {
            Pointer ptr = csManager.getCSVar(context, nw.getLValue());
            Obj newObj = heapModel.getObj(nw);
            Context heapContext = contextSelector.selectHeapContext(csMethod, newObj);
            workList.addEntry(ptr, PointsToSetFactory.make(csManager.getCSObj(heapContext, newObj)));

            return visitDefault(nw);
        }

        @Override
        public Void visit(Copy cp) {
            addPFGEdge(
                csManager.getCSVar(context, cp.getRValue()),
                csManager.getCSVar(context, cp.getLValue())
            );

            return visitDefault(cp);
        }

        @Override
        public Void visit(LoadField ld) {
            if(ld.isStatic()) {
                addPFGEdge(
                    csManager.getStaticField(ld.getFieldRef().resolve()),
                    csManager.getCSVar(context, ld.getLValue())
                );
            }

            return visitDefault(ld);
        }

        @Override
        public Void visit(StoreField st) {
            if(st.isStatic()) {
                addPFGEdge(
                    csManager.getCSVar(context, st.getRValue()),
                    csManager.getStaticField(st.getFieldRef().resolve())
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
            PointsToSet ptsrc = source.getPointsToSet();
            if(!ptsrc.isEmpty()) {
                workList.addEntry(target, ptsrc);
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
            // PointsToSet delta = new PointsToSet();
            // pts.objects()
            //         .filter(obj -> !ptr.getPointsToSet().contains(obj))
            //         .forEach(obj -> delta.addObject(obj));
            // propagate(ptr, delta);   
            PointsToSet delta = propagate(ptr, pts);
            if(ptr instanceof CSVar csVar) {
                delta.objects().forEach(obj -> {
                    csVar.getVar().getStoreFields().forEach(field -> {
                        addPFGEdge(
                            csManager.getCSVar(csVar.getContext(), field.getRValue()),
                            csManager.getInstanceField(obj, field.getFieldRef().resolve())
                        );
                    });

                    csVar.getVar().getLoadFields().forEach(field -> {
                        addPFGEdge(
                            csManager.getInstanceField(obj, field.getFieldRef().resolve()),
                            csManager.getCSVar(csVar.getContext(), field.getLValue())
                        );
                    });

                    csVar.getVar().getStoreArrays().forEach(field -> {
                        addPFGEdge(
                            csManager.getCSVar(csVar.getContext(), field.getRValue()),
                            csManager.getArrayIndex(obj)
                        );
                    });

                    csVar.getVar().getLoadArrays().forEach(field -> {
                        addPFGEdge(
                            csManager.getArrayIndex(obj),
                            csManager.getCSVar(csVar.getContext(), field.getLValue())
                        );
                    });

                    processCall(csVar, obj);

                    if(taintAnalysis.isTaint(obj.getObject())) {
                        taintInMethodArg.getOrDefault(csVar, new HashSet<>()).forEach(callsite -> {
                            CSCallSite csCallSite = csManager.getCSCallSite(csVar.getContext(), callsite);
                            if(callsite.getInvokeExp() instanceof InvokeInstanceExp iiexp) {
                                CSVar base = csManager.getCSVar(
                                    csCallSite.getContext(),
                                    iiexp.getBase()
                                );
                                base.getPointsToSet().forEach(baseObj -> {
                                    JMethod callee = resolveCallee(baseObj, callsite);
                                    taintAnalysis.makeTaintTransfers(csCallSite, callee, base).forEach((csVarr, taint) -> {
                                        workList.addEntry(csVarr,
                                            PointsToSetFactory.make(taint)
                                        );
                                    });
                                });
                            }else {
                                JMethod callee = resolveCallee(null, callsite);
                                taintAnalysis.makeTaintTransfers(csCallSite, callee, null).forEach((csVarr, taint) -> {
                                    workList.addEntry(
                                        csVarr,
                                        PointsToSetFactory.make(taint)
                                    );
                                });
                            }
                        });
                    }
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
        PointsToSet ptn = pointer.getPointsToSet();
        PointsToSet delta = PointsToSetFactory.make();
        pointsToSet.objects()
            .filter(obj -> !ptn.contains(obj))
            .forEach(obj -> delta.addObject(obj));
        if(!delta.isEmpty()) {
            ptn.addAll(delta);
            pointerFlowGraph.getSuccsOf(pointer).forEach(succ -> {
                workList.addEntry(succ, delta);
            });
        }
        return delta;
    }

    private void doProcessCall(CSCallSite csCallSite, CSMethod csCallee, CallKind callKind) {
        Context ct = csCallee.getContext();
        JMethod callee = csCallee.getMethod();
        Invoke callsite = csCallSite.getCallSite();
        CSObj taintObj = taintAnalysis.makeSource(
            callsite,
            csCallee.getMethod()
        );
        if(taintObj != null) {
            Var lVar = csCallSite.getCallSite().getLValue();
            if(lVar != null) {
                CSVar csVar = csManager.getCSVar(
                    csCallSite.getContext(),
                    lVar
                );
                workList.addEntry(
                    csVar,
                    PointsToSetFactory.make(taintObj)
                );
            }
        }

        if(callKind != null) {
            if(callGraph.addEdge(new Edge<>(callKind, csCallSite, csCallee))) {
                addReachable(csCallee);
                int argc = callee.getParamCount();
                assert argc == csCallSite.getCallSite().getRValue().getArgCount();
                for(int i = 0; i < argc; i++) {
                    addPFGEdge(
                        csManager.getCSVar(csCallSite.getContext(), csCallSite.getCallSite().getRValue().getArg(i)),
                        csManager.getCSVar(ct, callee.getIR().getParam(i))
                    );
                }
                Var lVar = csCallSite.getCallSite().getLValue();
                if(lVar != null) {
                    callee.getIR().getReturnVars().forEach(retVar -> {
                        addPFGEdge( 
                            csManager.getCSVar(ct, retVar),
                            csManager.getCSVar(csCallSite.getContext(), lVar)
                        );
                    });
                }
            }

            if(callsite.getInvokeExp() instanceof InvokeInstanceExp iiexp) {
                CSVar base = csManager.getCSVar(
                    csCallSite.getContext(),
                    iiexp.getBase()
                );
                taintAnalysis.makeTaintTransfers(csCallSite, callee, base).forEach((csVar, taint) -> {
                    propagate(csVar,
                        PointsToSetFactory.make(taint)
                    );
                });
            }else {
                taintAnalysis.makeTaintTransfers(csCallSite, callee, null).forEach((csVar, taint) -> {
                    propagate(
                        csVar,
                        PointsToSetFactory.make(taint)
                    );
                });
            }
        }
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        recv.getVar().getInvokes().forEach(callSite -> {
            JMethod callee = resolveCallee(recvObj, callSite);
            CallKind callKind = null;

            if(callSite.isVirtual()) callKind = CallKind.VIRTUAL;
            else if(callSite.isInterface()) callKind = CallKind.INTERFACE;
            else if(callSite.isSpecial()) callKind = CallKind.SPECIAL;

            CSCallSite csCallSite = csManager.getCSCallSite(recv.getContext(), callSite);
            Context ct = contextSelector.selectContext(csCallSite, recvObj, callee);
            workList.addEntry(
                csManager.getCSVar(ct, callee.getIR().getThis()),
                PointsToSetFactory.make(recvObj)
            );
            doProcessCall(
                csCallSite,
                csManager.getCSMethod(ct, callee),
                callKind
            );
        });
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
