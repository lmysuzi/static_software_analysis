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
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Pair;

import java.util.*;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

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
    }

    // TODO - finish me

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.
        handleTaintSink(taintFlows);
        return taintFlows;
    }

    public boolean isCSObjtainted(CSObj csObj) {
        return manager.isTaint(csObj.getObject());
    }

    public Obj handleTaintSource(Invoke invoke, JMethod method) {
        Obj ans = null;
        Source source = new Source(method, method.getReturnType());
        if (config.getSources().contains(source)) {
            ans = manager.makeTaint(invoke, method.getReturnType());
        }
        return ans;
    }

    public Set<Pair<Var, Obj>> handleTaintTransfer(CSCallSite csCallSite, JMethod method, CSVar csVar) {
        Invoke callSite = csCallSite.getCallSite();
        Var leftVar = callSite.getLValue();
        Set<Pair<Var, Obj>> ans = new HashSet<>();
        if (csVar != null) {
            if (leftVar != null) 
                handleBaseToResult(csVar, method, leftVar, ans);
            handleArgToBase(csVar, callSite, method, csCallSite.getContext(), ans);
        }
        if(leftVar!=null){
            handleArgToResult(callSite,method,leftVar,csCallSite.getContext(),ans);
        }
        
        return ans;
    }

    private void handleBaseToResult(CSVar csVar, JMethod method, Var leftVar, Set<Pair<Var, Obj>> ans) {
        Type type = method.getReturnType();
        TaintTransfer transfer = new TaintTransfer(method, TaintTransfer.BASE, TaintTransfer.RESULT, type);
        if (config.getTransfers().contains(transfer)) {
            for (CSObj obj : solver.getResult().getPointsToSet(csVar)) {
                if (manager.isTaint(obj.getObject())) {
                    ans.add(new Pair<>(leftVar,
                            manager.makeTaint(manager.getSourceCall(obj.getObject()), type)));
                }
            }
        }
    }

    private void handleArgToBase(CSVar csVar, Invoke invoke, JMethod method, Context context, Set<Pair<Var, Obj>> ans) {
        Type type = csVar.getType();
        for (int i = 0; i < invoke.getInvokeExp().getArgCount(); i++) {
            Var arg = invoke.getInvokeExp().getArg(i);
            TaintTransfer transfer = new TaintTransfer(method, i, TaintTransfer.BASE, type);
            if (config.getTransfers().contains(transfer)) {
                for (CSObj obj : solver.getResult().getPointsToSet(csManager.getCSVar(context, arg))) {
                    if (manager.isTaint(obj.getObject())) {
                        ans.add(new Pair<>(csVar.getVar(),
                                manager.makeTaint(manager.getSourceCall(obj.getObject()), type)));
                    }
                }
            }
        }
    }

    private void handleArgToResult(Invoke invoke,JMethod method,Var leftVar,Context context,Set<Pair<Var, Obj>> ans){
        List<Var> args = invoke.getInvokeExp().getArgs();
        Type type = method.getReturnType();
        for (int i = 0; i < invoke.getInvokeExp().getArgCount(); i++) {
            Var arg = invoke.getInvokeExp().getArg(i);
            TaintTransfer transfer = new TaintTransfer(method, i, TaintTransfer.RESULT, type);
            if (config.getTransfers().contains(transfer)) {
                for(CSObj obj : solver.getResult().getPointsToSet(csManager.getCSVar(context,arg))){
                    if (manager.isTaint(obj.getObject())) {
                        ans.add(new Pair<>(leftVar,
                                manager.makeTaint(manager.getSourceCall(obj.getObject()), type)));
                    }
                }
            }
        }
    }

    private void handleTaintSink(Set<TaintFlow> taintFlows){
        for(CSMethod csMethod:solver.getResult().getCSCallGraph().reachableMethods().toList()){
            for(CSCallSite csCallSite:solver.getResult().getCSCallGraph().getCallersOf(csMethod)){
                Invoke invoke = csCallSite.getCallSite();
                JMethod method = csMethod.getMethod();
                List<Var> args = invoke.getInvokeExp().getArgs();
                for(int i = 0;i < invoke.getInvokeExp().getArgCount();i ++){
                    Var arg = invoke.getInvokeExp().getArg(i);
                    Sink sink = new Sink(method, i);
                    if(config.getSinks().contains(sink)){
                        for(Obj obj:solver.getResult().getPointsToSet(arg)){
                            if(manager.isTaint(obj)){
                                taintFlows.add(new TaintFlow(manager.getSourceCall(obj),invoke,i));
                            }
                        }
                    }
                }
            }
        }
    }
}
