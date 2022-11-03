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

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.*;

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

        Queue<JMethod> workList = new LinkedList<>();
        workList.add(entry);
        while (!workList.isEmpty()) {
            JMethod method = workList.poll();
            if (callGraph.contains(method)) continue;
            callGraph.addReachableMethod(method);

            for (Invoke callSite :
                    callGraph.getCallSitesIn(method)) {
                Set<JMethod> targets = resolve(callSite);
                for (JMethod targetMethod :
                        targets) {
                    Edge<Invoke, JMethod> edge = new Edge<>(CallGraphs.getCallKind(callSite), callSite, targetMethod);
                    callGraph.addEdge(edge);
                    workList.add(targetMethod);
                }
            }
        }

        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        Set<JMethod> T = new HashSet<>();
        MethodRef methodRef = callSite.getMethodRef();
        Subsignature m = methodRef.getSubsignature();
        JClass jClass = methodRef.getDeclaringClass();
        CallKind callKind = CallGraphs.getCallKind(callSite);

        if (callKind == CallKind.VIRTUAL || callKind == CallKind.INTERFACE) {
            Queue<JClass> classes = new LinkedList<>();
            classes.add(jClass);
            while (!classes.isEmpty()) {
                JClass currentClass = classes.poll();
                JMethod jMethod = dispatch(currentClass, m);
                if (jMethod != null)
                    T.add(jMethod);
                classes.addAll(hierarchy.getDirectSubclassesOf(currentClass));
                classes.addAll(hierarchy.getDirectImplementorsOf(currentClass));
                classes.addAll(hierarchy.getDirectSubinterfacesOf(currentClass));
            }
        } else {
            JMethod jMethod = dispatch(jClass, m);
            if (jMethod != null)
                T.add(jMethod);
        }
        return T;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        while (jclass != null && (jclass.getDeclaredMethod(subsignature) == null
                || jclass.getDeclaredMethod(subsignature).isAbstract()))
            jclass = jclass.getSuperClass();
        if (jclass != null) return jclass.getDeclaredMethod(subsignature);
        return null;
    }
}
