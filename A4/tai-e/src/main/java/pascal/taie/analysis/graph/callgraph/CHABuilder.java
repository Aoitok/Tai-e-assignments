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
import pascal.taie.util.collection.Sets;

import java.util.ArrayDeque;
import java.util.Queue;
import java.util.Set;

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
        Queue<JMethod> worklist = new ArrayDeque<>();
        worklist.add(entry);
        while (!worklist.isEmpty()) {
            JMethod jmethod = worklist.poll();
            callGraph.addReachableMethod(jmethod);
            callGraph.callSitesIn(jmethod).forEach(callSite -> {
                CallKind callKind = CallGraphs.getCallKind(callSite);
                for (JMethod callee : resolve(callSite)) {
                    callGraph.addEdge(new Edge<>(callKind, callSite, callee));
                    if (!callGraph.contains(callee)) {
                        worklist.add(callee);
                    }
                }
            });
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        Set<JMethod> result = Sets.newSet();
        MethodRef methodRef = callSite.getMethodRef();
        JClass declaringClass = methodRef.getDeclaringClass();
        Subsignature subsignature = methodRef.getSubsignature();
        switch (CallGraphs.getCallKind(callSite)) {
            case STATIC:
                result.add(declaringClass.getDeclaredMethod(subsignature));
                break;
            case SPECIAL:
                JMethod jmethod = dispatch(declaringClass, subsignature);
                if (jmethod != null) {
                    result.add(jmethod);
                }
                break;
            case INTERFACE:
            case VIRTUAL:
                Queue<JClass> worklist = new ArrayDeque<>();
                Set<JClass> reached = Sets.newSet();
                worklist.add(declaringClass);
                while (!worklist.isEmpty()) {
                    JClass jclass = worklist.poll();
                    reached.add(jclass);
                    JMethod jmedhod = dispatch(jclass, subsignature);
                    if (jmedhod != null) {
                        result.add(jmedhod);
                    }
                    for (JClass subclass : hierarchy.getDirectSubclassesOf(jclass)) {
                        if (!reached.contains(subclass)) {
                            worklist.add(subclass);
                        }
                    }
                    if (jclass.isInterface()) {
                        for (JClass subinterface : hierarchy.getDirectSubinterfacesOf(jclass)) {
                            if (!reached.contains(subinterface)) {
                                worklist.add(subinterface);
                            }
                        }
                        for (JClass implementor : hierarchy.getDirectImplementorsOf(jclass)) {
                            if (!reached.contains(implementor)) {
                                worklist.add(implementor);
                            }
                        }
                    }
                }
                break;
            default:
                break;
        }
        return result;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     *         can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        if (jclass == null) {
            return null;
        }
        JMethod jmethod = jclass.getDeclaredMethod(subsignature);
        if (jmethod != null && !jmethod.isAbstract()) {
            return jmethod;
        }
        return dispatch(jclass.getSuperClass(), subsignature);
    }
}
