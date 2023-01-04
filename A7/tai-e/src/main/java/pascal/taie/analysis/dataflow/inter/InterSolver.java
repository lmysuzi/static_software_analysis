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
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.graph.icfg.ICFGEdge;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JClass;
import pascal.taie.util.collection.SetQueue;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

import static pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation.meetValue;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
        Set<Node> entryNodes = new HashSet<>();

        for (Method entryMethod : icfg.entryMethods().toList()) {
            Node entryNode = icfg.getEntryOf(entryMethod);
            entryNodes.add(entryNode);
            result.setInFact(entryNode, analysis.newBoundaryFact(entryNode));
            result.setOutFact(entryNode, analysis.newBoundaryFact(entryNode));
        }

        for (Node node : icfg) {
            if (entryNodes.contains(node)) continue;
            result.setInFact(node, analysis.newInitialFact());
            result.setOutFact(node, analysis.newInitialFact());
        }
    }

    private void doSolve() {
        workList = new LinkedList<>();

        for (Node node : icfg) {
            workList.add(node);
        }

        while (!workList.isEmpty()) {
            Node node = workList.poll();

            for (ICFGEdge<Node> inEdge : icfg.getInEdgesOf(node)) {
                Fact transferOut = analysis.transferEdge(inEdge, result.getOutFact(inEdge.getSource()));
                analysis.meetInto(transferOut, result.getInFact(node));
            }

            Stmt stmt = (Stmt) node;
            if(stmt instanceof StoreField storeField){
                handleStoreField(storeField, (CPFact) result.getInFact(node));
            }
            if(stmt instanceof StoreArray storeArray){
                handleStoreArray(storeArray,(CPFact) result.getInFact(node));
            }


            if (analysis.transferNode(node, result.getInFact(node), result.getOutFact(node))) {
                for (ICFGEdge<Node> outEdge : icfg.getOutEdgesOf(node)) {
                    Node outNode = outEdge.getTarget();
                    if (!workList.contains(outNode))
                        workList.add(outNode);
                }
            }
        }
    }

    private void handleStoreField(StoreField storeStmt, CPFact in){
        if(!ConstantPropagation.canHoldInt(storeStmt.getRValue()))
            return;

        FieldAccess fieldAccess= storeStmt.getFieldAccess();
        if(fieldAccess instanceof InstanceFieldAccess access){
            ConstantPropagation.pta.getPointsToSet((access.getBase())).forEach(obj -> {
                Pair<Obj, FieldRef> accessPair = new Pair<>(obj, storeStmt.getFieldRef());
                Value oldValue=ConstantPropagation.instanceValueMap.getOrDefault(accessPair,
                        Value.getUndef());
                Value newValue=ConstantPropagation.evaluate(storeStmt.getRValue(),in);
                newValue= meetValue(newValue,oldValue);
                ConstantPropagation.instanceValueMap.put(accessPair,newValue);
                if(!newValue.equals(oldValue)){
                    for(Var var : ConstantPropagation.objAliasMap.get(obj)){
                        var.getLoadFields().stream()
                                .filter(loadStmt -> loadStmt.getFieldAccess().getFieldRef().equals(storeStmt.getFieldRef()))
                                .forEach(loadStmt -> workList.offer((Node) loadStmt));
                    }
                }
            });
        }else if(fieldAccess instanceof StaticFieldAccess access){
            JClass jClass = access.getFieldRef().getDeclaringClass();
            Pair<JClass, FieldRef> accessPair = new Pair<>(jClass, storeStmt.getFieldRef());
            Value oldValue = ConstantPropagation.staticValueMap.getOrDefault(accessPair, Value.getUndef());
            Value newValue = ConstantPropagation.evaluate(storeStmt.getRValue(), in);
            newValue = ConstantPropagation.meetValue(oldValue, newValue);
            ConstantPropagation.staticValueMap.put(accessPair, newValue);
            if (!oldValue.equals(newValue)) {
                ConstantPropagation.staticMap.getOrDefault(accessPair, new HashSet<>()).forEach(loadStmt -> {
                    workList.offer((Node) loadStmt);
                });
            }
        }
    }

    private void handleStoreArray(StoreArray storeStmt,CPFact in){
        if(!ConstantPropagation.canHoldInt(storeStmt.getRValue()))
            return;

        ArrayAccess arrayAccess = storeStmt.getArrayAccess();
        Value index = ConstantPropagation.evaluate(arrayAccess.getIndex(), in);
        if(index.isUndef()) return;
        Var base = arrayAccess.getBase();
        ConstantPropagation.pta.getPointsToSet(base).forEach(obj -> {
            Pair<Obj, Value> accessPair = new Pair<>(obj, index);
            Value newValue = ConstantPropagation.evaluate(storeStmt.getRValue(), in);
            Value oldValue = ConstantPropagation.arrayValueMap.getOrDefault(accessPair, Value.getUndef());
            newValue = meetValue(oldValue, newValue);
            ConstantPropagation.arrayValueMap.put(accessPair, newValue);
            if(!oldValue.equals(newValue)){
                Set<Var> alias = ConstantPropagation.objAliasMap.get(obj);
                alias.forEach(var -> {
                    var.getLoadArrays().forEach(loadStmt -> workList.offer((Node) loadStmt));
                });
            }
        });
    }
}
