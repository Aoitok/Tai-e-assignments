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
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysiss;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JField;
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

    Solver(AnalysisOptions options, HeapModel heapModel,
            ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
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
        if (callGraph.contains(csMethod))
            return;
        callGraph.addReachableMethod(csMethod);
        StmtProcessor stmtProcessor = new StmtProcessor(csMethod);
        csMethod.getMethod().getIR().getStmts().forEach(stmt -> stmt.accept(stmtProcessor));
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

        @Override
        public Void visit(New stmt) {
            Obj obj = heapModel.getObj(stmt);
            Var var = stmt.getLValue();
            Context heapContext = contextSelector.selectHeapContext(csMethod, obj);
            workList.addEntry(csManager.getCSVar(context, var),
                    PointsToSetFactory.make(csManager.getCSObj(heapContext, obj)));
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            addPFGEdge(csManager.getCSVar(context, stmt.getRValue()), csManager.getCSVar(context, stmt.getLValue()));
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            JField field = stmt.getFieldRef().resolve();
            if (field.isStatic()) {
                CSVar csVar = csManager.getCSVar(context, stmt.getLValue());
                StaticField staticField = csManager.getStaticField(field);
                addPFGEdge(staticField, csVar);
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            JField field = stmt.getFieldRef().resolve();
            if (field.isStatic()) {
                CSVar csVar = csManager.getCSVar(context, stmt.getRValue());
                StaticField staticField = csManager.getStaticField(field);
                addPFGEdge(csVar, staticField);
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (!stmt.isStatic()) {
                return null;
            }
            CSCallSite csCallSite = csManager.getCSCallSite(context, stmt);
            JMethod callee = resolveCallee(null, stmt);
            Context targetContext = contextSelector.selectContext(csCallSite, callee);
            CSMethod csCallee = csManager.getCSMethod(targetContext, callee);
            if (!callGraph.addEdge(new Edge<>(CallKind.STATIC, csCallSite, csCallee))) {
                return null;
            }
            addReachable(csCallee);
            InvokeExp invokeExp = stmt.getInvokeExp();
            for (int i = 0; i < invokeExp.getArgCount(); i++) {
                Var param = callee.getIR().getParam(i);
                Var arg = invokeExp.getArg(i);
                addPFGEdge(csManager.getCSVar(context, arg), csManager.getCSVar(targetContext, param));
            }
            if (stmt.getDef().isPresent() && stmt.getDef().get() instanceof Var var) {
                for (Var returnVar : callee.getIR().getReturnVars()) {
                    addPFGEdge(csManager.getCSVar(targetContext, returnVar), csManager.getCSVar(context, var));
                }
                Type type = callee.getReturnType();
                if (taintAnalysis.isSource(callee, type)) {
                    workList.addEntry(csManager.getCSVar(context, var),
                            PointsToSetFactory.make(taintAnalysis.makeTaint(stmt, type)));
                }
            }
            taintAnalysis.transferTaint(callee, stmt, context, null);
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
            if (pointer instanceof CSVar csVar) {
                Var var = csVar.getVar();
                Context context = csVar.getContext();
                for (CSObj csObj : difference) {
                    for (StoreArray storeArray : var.getStoreArrays()) {
                        ArrayIndex arrayIndex = csManager.getArrayIndex(csObj);
                        addPFGEdge(csManager.getCSVar(context, storeArray.getRValue()), arrayIndex);
                    }
                    for (LoadArray loadArray : var.getLoadArrays()) {
                        ArrayIndex arrayIndex = csManager.getArrayIndex(csObj);
                        addPFGEdge(arrayIndex, csManager.getCSVar(context, loadArray.getLValue()));
                    }
                    for (StoreField storeField : var.getStoreFields()) {
                        JField field = storeField.getFieldRef().resolve();
                        if (!field.isStatic()) {
                            InstanceField instanceField = csManager.getInstanceField(csObj, field);
                            addPFGEdge(csManager.getCSVar(context, storeField.getRValue()), instanceField);
                        }
                    }
                    for (LoadField loadField : var.getLoadFields()) {
                        JField field = loadField.getFieldRef().resolve();
                        if (!field.isStatic()) {
                            InstanceField instanceField = csManager.getInstanceField(csObj, field);
                            addPFGEdge(instanceField, csManager.getCSVar(context, loadField.getLValue()));
                        }
                    }
                    processCall(csVar, csObj);
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
        PointsToSet difference = PointsToSetFactory.make();
        PointsToSet taints = PointsToSetFactory.make();
        for (CSObj csObj : pointsToSet) {
            if (!pt.contains(csObj)) {
                pt.addObject(csObj);
                difference.addObject(csObj);
                if (taintAnalysis.isTaint(csObj.getObject())) {
                    taints.addObject(csObj);
                }
            }
        }
        if (!difference.isEmpty()) {
            for (Pointer succ : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(succ, difference);
            }
            if (!taints.isEmpty()) {
                for (Pointer succ : taintAnalysis.getSuccsOfTFG(pointer)) {
                    workList.addEntry(succ, taints);
                }
            }
        }
        return difference;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        if (taintAnalysis.isTaint(recvObj.getObject())) {
            return;
        }
        for (Invoke invoke : recv.getVar().getInvokes()) {
            if (invoke.isStatic()) {
                continue;
            }
            Context context = recv.getContext();
            CSCallSite csCallSite = csManager.getCSCallSite(context, invoke);
            JMethod callee = resolveCallee(recvObj, invoke);
            Context targetContext = contextSelector.selectContext(csCallSite, recvObj, callee);
            CSMethod csCallee = csManager.getCSMethod(targetContext, callee);
            Var calleeThis = callee.getIR().getThis();
            workList.addEntry(csManager.getCSVar(targetContext, calleeThis), PointsToSetFactory.make(recvObj));
            CallKind callKind;
            if (invoke.isSpecial()) {
                callKind = CallKind.SPECIAL;
            } else if (invoke.isInterface()) {
                callKind = CallKind.INTERFACE;
            } else {
                callKind = CallKind.VIRTUAL;
            }
            if (callGraph.addEdge(new Edge<>(callKind, csCallSite, csCallee))) {
                addReachable(csCallee);
                InvokeExp invokeExp = invoke.getInvokeExp();
                for (int i = 0; i < invokeExp.getArgCount(); i++) {
                    Var param = callee.getIR().getParam(i);
                    Var arg = invokeExp.getArg(i);
                    addPFGEdge(csManager.getCSVar(context, arg), csManager.getCSVar(targetContext, param));
                }
                if (invoke.getDef().isPresent() && invoke.getDef().get() instanceof Var v) {
                    for (Var returnVar : callee.getIR().getReturnVars()) {
                        addPFGEdge(csManager.getCSVar(targetContext, returnVar), csManager.getCSVar(context, v));
                    }
                    Type type = callee.getReturnType();
                    if (taintAnalysis.isSource(callee, type)) {
                        workList.addEntry(csManager.getCSVar(context, v),
                                PointsToSetFactory.make(taintAnalysis.makeTaint(invoke, type)));
                    }
                }
                taintAnalysis.transferTaint(callee, invoke, context, recv);
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

    public void updateWorkList(Pointer pointer, PointsToSet pts) {
        workList.addEntry(pointer, pts);
    }
}
