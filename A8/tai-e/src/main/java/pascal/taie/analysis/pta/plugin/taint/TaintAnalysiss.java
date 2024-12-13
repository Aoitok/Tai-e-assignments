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

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;

import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    private final MultiMap<JMethod, Sink> toSinks = Maps.newMultiMap();

    private final MultiMap<JMethod, TaintTransfer> toTransfers = Maps.newMultiMap();

    private final MultiMap<JMethod, Type> toSourceTypes = Maps.newMultiMap();

    private final TaintFlowGraph taintFlowGraph = new TaintFlowGraph();

    private final class TaintFlowGraph {

        private final MultiMap<Pointer, Pointer> successors = Maps.newMultiMap();

        boolean addEdge(Pointer source, Pointer target) {
            return successors.put(source, target);
        }

        Set<Pointer> getSuccsOf(Pointer pointer) {
            return successors.get(pointer);
        }
    }

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

        config.getSinks().forEach(sink -> {
            toSinks.put(sink.method(), sink);
        });
        config.getTransfers().forEach(transfer -> {
            toTransfers.put(transfer.method(), transfer);
        });
        config.getSources().forEach(source -> {
            toSourceTypes.put(source.method(), source.type());
        });
    }

    private void addTFGEdge(Pointer source, Pointer target, Type taintType) {
        if (taintFlowGraph.addEdge(source, target)) {
            PointsToSet pts = PointsToSetFactory.make();
            for (CSObj csObj : source.getPointsToSet()) {
                if (isTaint(csObj.getObject())) {
                    pts.addObject(makeTaint(manager.getSourceCall(csObj.getObject()), taintType));
                }
            }
            if (!pts.isEmpty()) {
                solver.updateWorkList(target, pts);
            }
        }
    }

    public Set<Pointer> getSuccsOfTFG(Pointer pointer) {
        return taintFlowGraph.getSuccsOf(pointer);
    }

    public CSObj makeTaint(Invoke source, Type type) {
        return csManager.getCSObj(emptyContext, manager.makeTaint(source, type));
    }

    public boolean isTaint(Obj obj) {
        return manager.isTaint(obj);
    }

    public boolean isSource(JMethod method, Type type) {
        return toSourceTypes.contains(method, type);
    }

    public void transferTaint(JMethod callee, Invoke callSite, Context context, CSVar base) {
        for (TaintTransfer transfer : toTransfers.get(callee)) {
            int from = transfer.from();
            int to = transfer.to();
            Type type = transfer.type();
            if (from >= 0 && to == TaintTransfer.RESULT && callSite.getDef().isPresent()
                    && callSite.getDef().get() instanceof Var var) {
                addTFGEdge(csManager.getCSVar(context, callSite.getInvokeExp().getArg(from)),
                        csManager.getCSVar(context, var), type);
            } else if (base != null && from == TaintTransfer.BASE && callSite.getDef().isPresent()
                    && callSite.getDef().get() instanceof Var var) {
                addTFGEdge(base, csManager.getCSVar(context, var), type);
            } else if (base != null && to == TaintTransfer.BASE) {
                addTFGEdge(csManager.getCSVar(context, callSite.getInvokeExp().getArg(from)), base, type);
            }
        }
    }

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // You could query pointer analysis results you need via variable result.
        result.getCSCallGraph().edges().forEach(edge -> {
            CSCallSite csCallSite = edge.getCallSite();
            Invoke callSite = csCallSite.getCallSite();
            JMethod callee = edge.getCallee().getMethod();
            // Subsignature subsignature = callee.getSubsignature();
            for (Sink sink : toSinks.get(callee)) {
                int index = sink.index();
                Var var = callSite.getInvokeExp().getArg(index);
                CSVar csVar = csManager.getCSVar(csCallSite.getContext(), var);
                for (CSObj csObj : result.getPointsToSet(csVar)) {
                    Obj obj = csObj.getObject();
                    if (manager.isTaint(obj)) {
                        taintFlows.add(new TaintFlow(manager.getSourceCall(obj), callSite, index));
                    }
                }
            }

        });
        return taintFlows;
    }
}
