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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // Your task is to recognize dead code in ir and add it to deadCode
        analyzeUnreachableCode(deadCode, constants, cfg);

        analyzeDeadAssignment(deadCode, liveVars, cfg);
        //exit不应出现于死代码中
        deadCode.remove(cfg.getExit());
        return deadCode;
    }

    /**
     * analyze the unreachable code
     *
     * @param deadCode  deadCode
     * @param constants Constants
     * @param cfg       cfg
     */
    private void analyzeUnreachableCode(Set<Stmt> deadCode, DataflowResult<Stmt, CPFact> constants, CFG<Stmt> cfg) {
        Set<Stmt> traversedStmt = new HashSet<>();
        Queue<Stmt> queue = new LinkedList<>();

        queue.add(cfg.getEntry());
        //traverse the CFG
        while (!queue.isEmpty()) {
            Stmt stmt = queue.poll();
            if (traversedStmt.contains(stmt)) continue;
            traversedStmt.add(stmt);

            if (stmt instanceof If ifStmt) {
                ConditionExp conditionExp = ifStmt.getCondition();
                Value conditionResult = ConstantPropagation.evaluate(conditionExp, constants.getOutFact(stmt));
                boolean isConstant = conditionResult.isConstant();
                if (!isConstant) {
                    queue.addAll(cfg.getSuccsOf(stmt));
                    continue;
                }

                boolean isTrue = conditionResult.getConstant() == 1;
                for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
                    Stmt target = edge.getTarget();
                    if (edge.getKind() == Edge.Kind.IF_TRUE) {
                        if (isTrue) queue.add(target);
                    } else if (edge.getKind() == Edge.Kind.IF_FALSE) {
                        if (!isTrue) queue.add(target);
                    } else throw new RuntimeException("wrong edge");
                }
            } else if (stmt instanceof SwitchStmt switchStmt) {
                Var var = switchStmt.getVar();
                //Value caseValue = constants.getOutFact(stmt).get(var);
                Value caseValue = ConstantPropagation.evaluate(var, constants.getOutFact(stmt));

                boolean isConstant = caseValue.isConstant();
                if (!isConstant) {
                    queue.addAll(cfg.getSuccsOf(stmt));
                    continue;
                }
                if (!switchStmt.getCaseValues().contains(caseValue.getConstant())) {
                    queue.add(switchStmt.getDefaultTarget());
                    continue;
                }

                for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
                    Stmt target = edge.getTarget();
                    if (edge.getKind() == Edge.Kind.SWITCH_CASE) {
                        if (caseValue.getConstant() == edge.getCaseValue()) {
                            queue.add(target);
                            break;
                        }
                    }
                }
            } else {
                for (Edge<Stmt> edge : cfg.getOutEdgesOf(stmt)) {
                    queue.add(edge.getTarget());
                }
            }
        }

        //将未遍历过的点加入死代码中
        for (Stmt stmt : cfg) {
            if (!traversedStmt.contains(stmt))
                deadCode.add(stmt);
        }
    }

    /**
     * analyze the dead assignment
     *
     * @param deadCode deadCode
     * @param liveVars liveVars
     * @param cfg      cfg
     */
    private void analyzeDeadAssignment(Set<Stmt> deadCode, DataflowResult<Stmt, SetFact<Var>> liveVars, CFG<Stmt> cfg) {
        for (Stmt stmt : cfg) {
            if (stmt instanceof AssignStmt<?, ?> assignStmt) {
                LValue def = assignStmt.getLValue();
                if (def instanceof Var var) {
                    if (!liveVars.getOutFact(stmt).contains(var) && hasNoSideEffect(assignStmt.getRValue()))
                        deadCode.add(stmt);
                }
            }
        }
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
