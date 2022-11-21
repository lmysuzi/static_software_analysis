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
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

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
        if (callGraph.contains(method)) return;
        callGraph.addReachableMethod(method);
        for (Stmt stmt : method.getIR().getStmts()) {
            stmt.accept(stmtProcessor);
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        @Override
        public Void visit(New stmt) {
            workList.addEntry(pointerFlowGraph.getVarPtr(stmt.getLValue()),
                    new PointsToSet(heapModel.getObj(stmt)));
            return null;
        }

        public Void visit(Copy stmt) {
            addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue()),
                    pointerFlowGraph.getVarPtr(stmt.getLValue()));
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                addPFGEdge(pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve()),
                        pointerFlowGraph.getVarPtr(stmt.getLValue())
                );
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue()),
                        pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve())
                );
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                JMethod method = resolveCallee(null, stmt);

                CallKind callKind;
                if (stmt.isStatic()) callKind = CallKind.STATIC;
                else if (stmt.isInterface()) callKind = CallKind.INTERFACE;
                else if (stmt.isVirtual()) callKind = CallKind.VIRTUAL;
                else if (stmt.isSpecial()) callKind = CallKind.SPECIAL;
                else return null;

                Edge<Invoke, JMethod> edge = new Edge<>(callKind, stmt, method);
                if (callGraph.addEdge(edge)) {
                    addReachable(method);
                    for (int i = 0; i < method.getParamCount(); i++) {
                        addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue().getArg(i)),
                                pointerFlowGraph.getVarPtr(method.getIR().getParam(i)));
                    }
                    for (Var ret : method.getIR().getReturnVars()) {
                        addPFGEdge(pointerFlowGraph.getVarPtr(ret),
                                pointerFlowGraph.getVarPtr(stmt.getLValue()));
                    }
                }
            }
            return null;
        }

    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        if (!pointerFlowGraph.addEdge(source, target))
            return;
        if (!source.getPointsToSet().isEmpty()) {
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

            if (entry.pointer() instanceof VarPtr varPtr) {
                Var var = varPtr.getVar();
                for (Obj obj : differenceSet) {
                    for (StoreField stmt : var.getStoreFields()) {
                        addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue()),
                                pointerFlowGraph.getInstanceField(obj,
                                        stmt.getFieldAccess().getFieldRef().resolve()));
                    }
                    for (LoadField stmt : var.getLoadFields()) {
                        addPFGEdge(pointerFlowGraph.getInstanceField(obj,
                                        stmt.getFieldAccess().getFieldRef().resolve()),
                                pointerFlowGraph.getVarPtr(stmt.getLValue()));
                    }
                    for (StoreArray stmt : var.getStoreArrays()) {
                        addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue()),
                                pointerFlowGraph.getArrayIndex(obj));
                    }
                    for (LoadArray stmt : var.getLoadArrays()) {
                        addPFGEdge(pointerFlowGraph.getArrayIndex(obj),
                                pointerFlowGraph.getVarPtr(stmt.getLValue()));
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
        PointsToSet differenceSet = new PointsToSet();

        for (Obj obj : pointsToSet) {
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
     * @param var  the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        for (Invoke invoke : var.getInvokes()) {
            JMethod m = resolveCallee(recv, invoke);
            workList.addEntry(pointerFlowGraph.getVarPtr(m.getIR().getThis()), new PointsToSet(recv));

            CallKind callKind;
            if (invoke.isStatic()) callKind = CallKind.STATIC;
            else if (invoke.isInterface()) callKind = CallKind.INTERFACE;
            else if (invoke.isVirtual()) callKind = CallKind.VIRTUAL;
            else if (invoke.isSpecial()) callKind = CallKind.SPECIAL;
            else continue;

            Edge<Invoke, JMethod> edge = new Edge<>(callKind, invoke, m);
            if (callGraph.addEdge(edge)) {
                addReachable(m);
                for (int i = 0; i < m.getParamCount(); i++) {
                    addPFGEdge(pointerFlowGraph.getVarPtr(invoke.getRValue().getArg(i)),
                            pointerFlowGraph.getVarPtr(m.getIR().getParam(i)));
                }
                if (invoke.getLValue() != null) {
                    for (Var ret : m.getIR().getReturnVars()) {
                        addPFGEdge(pointerFlowGraph.getVarPtr(ret),
                                pointerFlowGraph.getVarPtr(invoke.getLValue()));
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
