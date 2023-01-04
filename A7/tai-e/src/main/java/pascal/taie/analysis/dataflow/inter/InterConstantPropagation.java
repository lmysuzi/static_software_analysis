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

import jas.Pair;
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
import pascal.taie.ir.exp.*;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        // You can do initialization work here
        ConstantPropagation.pta = World.get().getResult(ptaId);
        ConstantPropagation.pta.getVars().forEach(var -> {
            ConstantPropagation.pta.getPointsToSet(var).forEach(obj -> {
                if(!ConstantPropagation.objAliasMap.containsKey(obj)){
                    ConstantPropagation.objAliasMap.put(obj, new HashSet<>());
                }
                ConstantPropagation.objAliasMap.get(obj).add(var);
            });
        });
        icfg.getNodes().forEach(stmt -> {
            if(stmt instanceof LoadField s && s.getFieldAccess() instanceof StaticFieldAccess access){
                Pair<JClass, FieldRef> accessPair = new Pair<>(access.getFieldRef().getDeclaringClass(), access.getFieldRef());
                if(!ConstantPropagation.staticMap.containsKey(accessPair)){
                    ConstantPropagation.staticMap.put(accessPair,new HashSet<>());
                }
                ConstantPropagation.staticMap.get(accessPair).add(s);
            }
        });
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
        CPFact outOld = out.copy();

        for (Var key : in.keySet()) {
            out.update(key, in.get(key));
        }

        return !outOld.equals(out);
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        return cp.transferNode(stmt,in,out);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        CPFact cpFact = out.copy();
        Stmt source = edge.getSource();
        if (source.getDef().isPresent()) {
            LValue def = source.getDef().get();
            if (def instanceof Var var)
                cpFact.remove(var);
        }

        return cpFact;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        CPFact cpFact = new CPFact();
        Invoke invoke = (Invoke) edge.getSource();
        InvokeExp invokeExp = invoke.getInvokeExp();
        IR ir = edge.getCallee().getIR();

        for (int i = 0; i < invokeExp.getArgCount(); i++) {
            Var param = ir.getParam(i);
            Value value = callSiteOut.get(invokeExp.getArg(i));
            if (ConstantPropagation.canHoldInt(param)) {
                cpFact.update(param, value);
            }
        }
        return cpFact;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        CPFact cpFact = new CPFact();
        Invoke invoke = (Invoke) edge.getCallSite();
        Var returnVar = invoke.getLValue();
        Value returnValue = Value.getUndef();

        if (returnVar == null) return cpFact;

        for (Var var : edge.getReturnVars()) {
            Value value = returnOut.get(var);
            returnValue = cp.meetValue(returnValue, value);
        }

        cpFact.update(returnVar, returnValue);

        return cpFact;
    }


}
