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
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
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

        for (Stmt stmt : csMethod.getMethod().getIR().getStmts()) {
            stmt.accept(new StmtProcessor(csMethod));
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
        public Void visit(New stmt) {
            Pointer ptr = csManager.getCSVar(context, stmt.getLValue());
            Obj obj = heapModel.getObj(stmt);
            Context ctx = contextSelector.selectHeapContext(csMethod, obj);
            PointsToSet pts = PointsToSetFactory.make(csManager.getCSObj(ctx, obj));
            workList.addEntry(ptr, pts);
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            addPFGEdge(csManager.getCSVar(context, stmt.getRValue()),
                    csManager.getCSVar(context, stmt.getLValue()));
            return null;
        }

        @Override
        public Void visit(Invoke callsite) {
            if (callsite.isStatic()) {
                JMethod m = resolveCallee(null, callsite);
                CSCallSite csite = csManager.getCSCallSite(context, callsite);
                Context ct = contextSelector.selectContext(csite, m);
                CSMethod cm = csManager.getCSMethod(ct, m);
                Context c = csite.getContext();

                //processSingleCall(csCallSite, csManager.getCSMethod(calleeContext, callee));
                if (!callGraph.getCalleesOf(csite).contains(cm)) {

                    callGraph.addEdge(new Edge<>(CallKind.STATIC, csite, cm));
                    addReachable(cm);
                    List<Var> args = cm.getMethod().getIR().getParams();
                    for (int i = 0; i < args.size(); i++) {
                        addPFGEdge(csManager.getCSVar(c, callsite.getRValue().getArg(i)),
                                csManager.getCSVar(ct, args.get(i)));
                    }
                    if (callsite.getLValue() != null) {
                        for (Var rv : m.getIR().getReturnVars()) {
                            addPFGEdge(csManager.getCSVar(ct, rv), csManager.getCSVar(c, callsite.getLValue()));
                        }
                    }
                }
            }

            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                addPFGEdge(csManager.getCSVar(context, stmt.getRValue()),
                        csManager.getStaticField(stmt.getFieldRef().resolve()));
            }
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                addPFGEdge(csManager.getStaticField(stmt.getFieldRef().resolve()),
                        csManager.getCSVar(context, stmt.getLValue()));
            }
            return null;
        }

    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        if (pointerFlowGraph.addEdge(source, target)) {
            if (!source.getPointsToSet().isEmpty())
                workList.addEntry(target, source.getPointsToSet());
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            PointsToSet differenceSet = propagate(entry.pointer(), entry.pointsToSet());

            if (entry.pointer() instanceof CSVar csVar) {
                Var x = csVar.getVar();
                for (CSObj obj : differenceSet) {
                    for (StoreField stmt : x.getStoreFields()) {
                        addPFGEdge(csManager.getCSVar(csVar.getContext(), stmt.getRValue()),
                                csManager.getInstanceField(obj, stmt.getFieldAccess().getFieldRef().resolve()));
                    }
                    for (LoadField stmt : x.getLoadFields()) {
                        addPFGEdge(csManager.getInstanceField(obj, stmt.getFieldAccess().getFieldRef().resolve()),
                                csManager.getCSVar(csVar.getContext(), stmt.getLValue()));
                    }
                    for (StoreArray stmt : x.getStoreArrays()) {
                        addPFGEdge(csManager.getCSVar(csVar.getContext(), stmt.getRValue()),
                                csManager.getArrayIndex(obj));
                    }
                    for (LoadArray stmt : x.getLoadArrays()) {
                        addPFGEdge(csManager.getArrayIndex(obj),
                                csManager.getCSVar(csVar.getContext(), stmt.getLValue()));
                    }
                    processCall(csVar, obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet differenceSet = PointsToSetFactory.make();

        for (CSObj obj : pointsToSet) {
            if (pointer.getPointsToSet().addObject(obj))
                differenceSet.addObject(obj);
        }

        if (!differenceSet.isEmpty()) {
            for (Pointer succ : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(succ, differenceSet);
            }
        }

        return differenceSet;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        Var var = recv.getVar();
        for (Invoke invoke : var.getInvokes()) {
            JMethod m = resolveCallee(recvObj, invoke);
            CSCallSite callSite = csManager.getCSCallSite(recv.getContext(), invoke);
            Context ct = contextSelector.selectContext(callSite, recvObj, m);
            CSMethod csMethod = csManager.getCSMethod(ct, m);
            workList.addEntry(csManager.getCSVar(ct, m.getIR().getThis()),
                    PointsToSetFactory.make(recvObj));

            CallKind callKind;
            if (invoke.isStatic()) callKind = CallKind.STATIC;
            else if (invoke.isInterface()) callKind = CallKind.INTERFACE;
            else if (invoke.isVirtual()) callKind = CallKind.VIRTUAL;
            else if (invoke.isSpecial()) callKind = CallKind.SPECIAL;
            else continue;

            if (callGraph.addEdge(new Edge<>(callKind, callSite, csMethod))) {
                addReachable(csMethod);
                for (int i = 0; i < m.getParamCount(); i++) {
                    addPFGEdge(csManager.getCSVar(recv.getContext(), invoke.getRValue().getArg(i)),
                            csManager.getCSVar(ct, m.getIR().getParam(i)));
                }
                if (invoke.getLValue() != null) {
                    for (Var ret : m.getIR().getReturnVars()) {
                        addPFGEdge(csManager.getCSVar(ct, ret),
                                csManager.getCSVar(recv.getContext(), invoke.getLValue()));
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
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
