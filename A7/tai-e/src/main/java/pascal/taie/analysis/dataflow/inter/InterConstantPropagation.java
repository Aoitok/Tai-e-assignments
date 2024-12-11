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

import java.util.Set;

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    private final MultiMap<Var, Var> aliases = Maps.newMultiMap();
    private final MultiMap<JField, LoadField> toLoadFields = Maps.newMultiMap();
    private final MultiMap<JField, StoreField> toStoreFields = Maps.newMultiMap();

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        PointerAnalysisResult pta = World.get().getResult(ptaId);
        // You can do initialization work here
        for (Var var1 : pta.getVars()) {
            Set<Obj> pts1 = pta.getPointsToSet(var1);
            for (Var var2 : pta.getVars()) {
                Set<Obj> pts2 = pta.getPointsToSet(var2);
                for (Obj obj : pts2) {
                    if (pts1.contains(obj)) {
                        aliases.put(var1, var2);
                        break;
                    }
                }
            }
        }
        for (Stmt stmt : icfg) {
            if (stmt instanceof LoadField loadField && loadField.isStatic()) {
                JField field = loadField.getFieldRef().resolve();
                toLoadFields.put(field, loadField);
            } else if (stmt instanceof StoreField storeField && storeField.isStatic()) {
                JField field = storeField.getFieldRef().resolve();
                toStoreFields.put(field, storeField);
            }
        }
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        return out.copyFrom(in);
    }

    private boolean isArrayAlias(Value value1, Value value2) {
        if (value1.isUndef() || value2.isUndef()) {
            return false;
        }
        if (value1.isConstant() && value2.isConstant()) {
            return value1.getConstant() == value2.getConstant();
        }
        return true;
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        if (stmt instanceof LoadField loadField) {
            if (loadField.getDef().isPresent() && loadField.getDef().get() instanceof Var var
                    && ConstantPropagation.canHoldInt(var)) {
                CPFact result = in.copy();
                JField field = loadField.getFieldRef().resolve();
                if (loadField.getFieldAccess() instanceof InstanceFieldAccess instanceField) {
                    Var base = instanceField.getBase();
                    for (Var alias : aliases.get(base)) {
                        for (StoreField storeField : alias.getStoreFields()) {
                            if (!storeField.getFieldRef().resolve().equals(field)) {
                                continue;
                            }
                            CPFact storeFieldIn = solver.getDataflowResult().getInFact(storeField);
                            Value newValue = storeFieldIn.get(storeField.getRValue());
                            result.update(var, cp.meetValue(result.get(var), newValue));
                        }
                    }
                } else {
                    for (StoreField storeField : toStoreFields.get(field)) {
                        CPFact storeFieldIn = solver.getDataflowResult().getInFact(storeField);
                        Value newValue = storeFieldIn.get(storeField.getRValue());
                        result.update(var, cp.meetValue(result.get(var), newValue));
                    }
                }
                return out.copyFrom(result);
            }
        } else if (stmt instanceof StoreField storeField) {
            if (ConstantPropagation.canHoldInt(storeField.getRValue())) {
                JField field = storeField.getFieldRef().resolve();
                if (storeField.getFieldAccess() instanceof InstanceFieldAccess instanceField) {
                    Var base = instanceField.getBase();
                    for (Var alias : aliases.get(base)) {
                        for (LoadField loadField : alias.getLoadFields()) {
                            if (loadField.getFieldRef().resolve().equals(field)) {
                                solver.updateWorkList(loadField);
                            }
                        }
                    }
                } else {
                    for (LoadField loadField : toLoadFields.get(field)) {
                        solver.updateWorkList(loadField);
                    }
                }
            }
        } else if (stmt instanceof LoadArray loadArray) {
            if (loadArray.getDef().isPresent() && loadArray.getDef().get() instanceof Var var
                    && ConstantPropagation.canHoldInt(var)) {
                CPFact result = in.copy();
                ArrayAccess array = loadArray.getArrayAccess();
                Var base = array.getBase();
                for (Var alias : aliases.get(base)) {
                    for (StoreArray storeArray : alias.getStoreArrays()) {
                        CPFact storeArrayIn = solver.getDataflowResult().getInFact(storeArray);
                        CPFact loadArrayIn = solver.getDataflowResult().getInFact(loadArray);
                        Value value1 = storeArrayIn.get(storeArray.getArrayAccess().getIndex());
                        Value value2 = loadArrayIn.get(array.getIndex());
                        if (isArrayAlias(value1, value2)) {
                            Value newValue = storeArrayIn.get(storeArray.getRValue());
                            result.update(var, cp.meetValue(result.get(var), newValue));
                        }
                    }
                }
                return out.copyFrom(result);
            }
        } else if (stmt instanceof StoreArray storeArray) {
            if (ConstantPropagation.canHoldInt(storeArray.getRValue())) {
                Var base = storeArray.getArrayAccess().getBase();
                for (Var alias : aliases.get(base)) {
                    for (LoadArray loadArray : alias.getLoadArrays()) {
                        solver.updateWorkList(loadArray);
                    }
                }
            }
        }
        return cp.transferNode(stmt, in, out);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        CPFact result = out.copy();
        Stmt invoke = edge.getSource();
        if (invoke.getDef().isPresent() && invoke.getDef().get() instanceof Var var) {
            result.remove(var);
        }
        return result;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        CPFact result = newInitialFact();
        JMethod callee = edge.getCallee();
        InvokeExp invokeExp = ((Invoke) edge.getSource()).getInvokeExp();
        for (int i = 0; i < invokeExp.getArgCount(); i++) {
            Var param = callee.getIR().getParam(i);
            Var arg = invokeExp.getArg(i);
            result.update(param, callSiteOut.get(arg));
        }
        return result;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        CPFact result = newInitialFact();
        Stmt callSite = edge.getCallSite();
        if (callSite.getDef().isPresent() &&
                callSite.getDef().get() instanceof Var var) {
            for (Var returnVar : edge.getReturnVars()) {
                result.update(var, cp.meetValue(result.get(var), returnOut.get(returnVar)));
            }
        }
        return result;
    }
}
