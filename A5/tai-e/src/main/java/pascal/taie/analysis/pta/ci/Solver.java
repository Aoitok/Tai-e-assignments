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

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

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
        if (callGraph.contains(method))
            return;
        callGraph.addReachableMethod(method);
        method.getIR().getStmts().forEach(stmt -> stmt.accept(stmtProcessor));
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // if you choose to implement addReachable()
        // via visitor pattern, then finish me
        @Override
        public Void visit(New stmt) {
            Obj obj = heapModel.getObj(stmt);
            Var var = stmt.getLValue();
            VarPtr varPtr = pointerFlowGraph.getVarPtr(var);
            workList.addEntry(varPtr, new PointsToSet(obj));
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue()), pointerFlowGraph.getVarPtr(stmt.getLValue()));
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            JField field = stmt.getFieldRef().resolve();
            if (field.isStatic()) {
                VarPtr varPtr = pointerFlowGraph.getVarPtr(stmt.getLValue());
                StaticField staticField = pointerFlowGraph.getStaticField(field);
                addPFGEdge(staticField, varPtr);
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            JField field = stmt.getFieldRef().resolve();
            if (field.isStatic()) {
                VarPtr varPtr = pointerFlowGraph.getVarPtr(stmt.getRValue());
                StaticField staticField = pointerFlowGraph.getStaticField(field);
                addPFGEdge(varPtr, staticField);
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (!stmt.isStatic()) {
                return null;
            }
            JMethod callee = resolveCallee(null, stmt);
            if (!callGraph.addEdge(new Edge<>(CallKind.STATIC, stmt, callee))) {
                return null;
            }
            addReachable(callee);
            InvokeExp invokeExp = stmt.getInvokeExp();
            for (int i = 0; i < invokeExp.getArgCount(); i++) {
                Var param = callee.getIR().getParam(i);
                Var arg = invokeExp.getArg(i);
                addPFGEdge(pointerFlowGraph.getVarPtr(arg), pointerFlowGraph.getVarPtr(param));
            }
            if (stmt.getDef().isPresent() && stmt.getDef().get() instanceof Var var) {
                for (Var returnVar : callee.getIR().getReturnVars()) {
                    addPFGEdge(pointerFlowGraph.getVarPtr(returnVar), pointerFlowGraph.getVarPtr(var));
                }
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        if (pointerFlowGraph.addEdge(source, target)) {
            PointsToSet pts = source.getPointsToSet();
            if (!pts.isEmpty()) {
                workList.addEntry(target, pts);
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            Pointer pointer = entry.pointer();
            PointsToSet difference = propagate(pointer, entry.pointsToSet());
            if (pointer instanceof VarPtr varPtr) {
                Var var = varPtr.getVar();
                for (Obj obj : difference) {
                    for (StoreArray storeArray : var.getStoreArrays()) {
                        addPFGEdge(pointerFlowGraph.getVarPtr(storeArray.getRValue()),
                                pointerFlowGraph.getArrayIndex(obj));
                    }
                    for (LoadArray loadArray : var.getLoadArrays()) {
                        addPFGEdge((pointerFlowGraph.getArrayIndex(obj)),
                                pointerFlowGraph.getVarPtr(loadArray.getLValue()));
                    }
                    for (StoreField storeField : var.getStoreFields()) {
                        JField field = storeField.getFieldRef().resolve();
                        if (!field.isStatic()) {
                            addPFGEdge(pointerFlowGraph.getVarPtr(storeField.getRValue()),
                                    pointerFlowGraph.getInstanceField(obj, field));
                        }
                    }
                    for (LoadField loadField : var.getLoadFields()) {
                        JField field = loadField.getFieldRef().resolve();
                        if (!field.isStatic()) {
                            addPFGEdge(pointerFlowGraph.getInstanceField(obj, field),
                                    pointerFlowGraph.getVarPtr(loadField.getLValue()));
                        }
                    }
                    processCall(var, obj);
                }
            }

        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet pt = pointer.getPointsToSet();
        PointsToSet difference = new PointsToSet();
        for (Obj obj : pointsToSet) {
            if (!pt.contains(obj)) {
                pt.addObject(obj);
                difference.addObject(obj);
            }
        }
        if (!difference.isEmpty()) {
            for (Pointer succ : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(succ, difference);
            }
        }
        return difference;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var  the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        for (Invoke invoke : var.getInvokes()) {
            if (invoke.isStatic()) {
                continue;
            }
            JMethod callee = resolveCallee(recv, invoke);
            Var calleeThis = callee.getIR().getThis();
            workList.addEntry(pointerFlowGraph.getVarPtr(calleeThis), new PointsToSet(recv));
            CallKind callKind;
            if (invoke.isSpecial()) {
                callKind = CallKind.SPECIAL;
            } else if (invoke.isInterface()) {
                callKind = CallKind.INTERFACE;
            } else {
                callKind = CallKind.VIRTUAL;
            }
            if (callGraph.addEdge(new Edge<>(callKind, invoke, callee))) {
                addReachable(callee);
                InvokeExp invokeExp = invoke.getInvokeExp();
                for (int i = 0; i < invokeExp.getArgCount(); i++) {
                    Var param = callee.getIR().getParam(i);
                    Var arg = invokeExp.getArg(i);
                    addPFGEdge(pointerFlowGraph.getVarPtr(arg), pointerFlowGraph.getVarPtr(param));
                }
                if (invoke.getDef().isPresent() && invoke.getDef().get() instanceof Var v) {
                    for (Var returnVar : callee.getIR().getReturnVars()) {
                        addPFGEdge(pointerFlowGraph.getVarPtr(returnVar), pointerFlowGraph.getVarPtr(v));
                    }
                }
            }
        }
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
