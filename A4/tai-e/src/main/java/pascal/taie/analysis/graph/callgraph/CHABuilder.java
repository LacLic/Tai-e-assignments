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

package pascal.taie.analysis.graph.callgraph;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me
        Queue<JMethod> worklist = new LinkedList<>(); // WL
        Set<JMethod> isVisited = new HashSet<>();    // RM
        worklist.add(entry);
        while(!worklist.isEmpty()) {
            JMethod thiz = worklist.poll();
            if(isVisited.contains(thiz)) continue;

            isVisited.add(thiz);
            callGraph.addReachableMethod(thiz);
            for(Invoke callSite : callGraph.getCallSitesIn(thiz)) {
                for(JMethod to : resolve(callSite)) {
                    callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(callSite), callSite, to));
                    worklist.add(to);
                }
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod> res = new HashSet<>();
        MethodRef methodRef = callSite.getMethodRef();
        if(CallGraphs.getCallKind(callSite) == CallKind.STATIC) {
            res.add(methodRef.getDeclaringClass().getDeclaredMethod(methodRef.getSubsignature()));
        }else if(CallGraphs.getCallKind(callSite) == CallKind.SPECIAL) {
            res.add(dispatch(methodRef.getDeclaringClass(), methodRef.getSubsignature()));
        }else if(CallGraphs.getCallKind(callSite) == CallKind.INTERFACE || CallGraphs.getCallKind(callSite) == CallKind.VIRTUAL) {
            Queue<JClass> q = new LinkedList<>();
            q.add(methodRef.getDeclaringClass());
            Subsignature subsignature = methodRef.getSubsignature();
            while(!q.isEmpty()) {
                JClass jc = q.poll();
                hierarchy.getDirectSubclassesOf(jc).forEach((e) -> q.add(e));
                hierarchy.getDirectSubinterfacesOf(jc).forEach((e) -> q.add(e));
                res.add(dispatch(jc, subsignature));
            }
        }else {
            assert(false);
        }
        return res;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        JMethod res = jclass.getDeclaredMethod(subsignature);
        if(res == null) {
            JClass superClass = jclass.getSuperClass();
            if(superClass == null) {
                res = null;
            }else {
                res = dispatch(superClass, subsignature);
            }
        }
        return res;
    }
}
