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

package pascal.taie.analysis.dataflow.analysis.constprop;

import jas.Pair;
import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.Set;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public static final Map<Obj, Set<Var>> objAliasMap = new HashMap<>();

    public static final Map<Pair<Obj, FieldRef>, Value> instanceValueMap = new HashMap<>();

    public static final Map<Pair<JClass, FieldRef>, Value> staticValueMap = new HashMap<>();

    public static final Map<Pair<Obj, Value>, Value> arrayValueMap = new HashMap<>();

    public static final Map<Pair<JClass,FieldRef>,Set<LoadField>> staticMap = new HashMap<>();

    public static PointerAnalysisResult pta;

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        CPFact boundaryFact = new CPFact();
        for (Var param : cfg.getIR().getParams()) {
            if (canHoldInt(param))
                boundaryFact.update(param, Value.getNAC());
        }
        return boundaryFact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        for (Var key : fact.keySet()) {
            //target???????????????key???????????????undef
            if (target.get(key).isUndef())
                target.update(key, fact.get(key));
            else target.update(key, meetValue(fact.get(key), target.get(key)));
        }
    }

    /**
     * Meets two Values.
     */
    public static Value meetValue(Value v1, Value v2) {
        Value ans;
        if (v1.isNAC() || v2.isNAC())
            ans = Value.getNAC();
        else if (v1.isConstant() && v2.isConstant()) {
            if (v1.equals(v2))
                ans = Value.makeConstant(v1.getConstant());
            else ans = Value.getNAC();
        }
        //????????????UNDEF
        else if (v1.isConstant())
            ans = Value.makeConstant(v1.getConstant());
        else if (v2.isConstant())
            ans = Value.makeConstant(v2.getConstant());
        else ans = Value.getUndef();
        return ans;
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        boolean flag = false;

        CPFact outOld = out.copy();

        for (Var key : in.keySet()) {
            out.update(key, in.get(key));
        }

        DefinitionStmt<?, ?> definitionStmt;
        if (stmt instanceof DefinitionStmt<?, ?>)
            definitionStmt = (DefinitionStmt<?, ?>) stmt;
        else return !outOld.equals(out);

        LValue def = definitionStmt.getLValue();
        Exp exp = definitionStmt.getRValue();
        Value value = evaluate(exp, in);
        if (def != null)
            if (def instanceof Var && canHoldInt((Var) def))
                out.update((Var) def, value);

        if (!outOld.equals(out)) flag = true;

        return flag;
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Compute result according to op and v1,v2
     *
     * @param op the operator
     * @param v1 the operand1
     * @param v2 the operand2
     * @return the result
     */
    private static int compute(BinaryExp.Op op, int v1, int v2) {
        return switch (op.toString()) {
            case "+" -> v1 + v2;
            case "-" -> v1 - v2;
            case "*" -> v1 * v2;
            case "/" -> v1 / v2;
            case "%" -> v1 % v2;
            case "==" -> (v1 == v2) ? 1 : 0;
            case "!=" -> (v1 != v2) ? 1 : 0;
            case "<" -> (v1 < v2) ? 1 : 0;
            case ">" -> (v1 > v2) ? 1 : 0;
            case "<=" -> (v1 <= v2) ? 1 : 0;
            case ">=" -> (v1 >= v2) ? 1 : 0;
            case "<<" -> v1 << v2;
            case ">>" -> v1 >> v2;
            case ">>>" -> v1 >>> v2;
            case "&" -> v1 & v2;
            case "|" -> v1 | v2;
            case "^" -> v1 ^ v2;
            default -> 0;
        };
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        Value ans = Value.getUndef();
        if (exp instanceof Var) {
            ans = in.get((Var) exp);
        } else if (exp instanceof IntLiteral) {
            ans = Value.makeConstant(((IntLiteral) exp).getValue());
        } else if (exp instanceof BinaryExp) {
            Var operand1 = ((BinaryExp) exp).getOperand1();
            Var operand2 = ((BinaryExp) exp).getOperand2();
            Value value1 = in.get(operand1);
            Value value2 = in.get(operand2);
            if (value1.isConstant() && value2.isConstant()) {
                if (value2.getConstant() == 0 &&
                        (Objects.equals(((BinaryExp) exp).getOperator().toString(), "/") ||
                                Objects.equals(((BinaryExp) exp).getOperator().toString(), "%")))
                    ans = Value.getUndef();
                else ans = Value.makeConstant(compute(((BinaryExp) exp).getOperator()
                        , value1.getConstant(), value2.getConstant()));
            } else if (value1.isNAC() || value2.isNAC()) {
                //?????????????????????0???????????????????????????
                if (value2.isConstant() && value2.getConstant() == 0 &&
                        (Objects.equals(((BinaryExp) exp).getOperator().toString(), "/") ||
                                Objects.equals(((BinaryExp) exp).getOperator().toString(), "%")))
                    ans = Value.getUndef();
                else ans = Value.getNAC();
            } else {
                ans = Value.getUndef();
            }
        } else if (exp instanceof InstanceFieldAccess fieldAccess) {
            for (Obj obj : pta.getPointsToSet(fieldAccess.getBase())) {
                ans = meetValue(ans,
                        instanceValueMap.getOrDefault(new Pair<>(obj, fieldAccess.getFieldRef()), Value.getUndef()));
            }
        } else if (exp instanceof StaticFieldAccess fieldAccess) {
            ans = staticValueMap.getOrDefault(new Pair<>(fieldAccess.getFieldRef().getDeclaringClass(),
                    fieldAccess.getFieldRef()), Value.getUndef());
        } else if (exp instanceof ArrayAccess arrayAccess) {
            Value index = evaluate(arrayAccess.getIndex(), in);
            if (index.isConstant()) {
                for (Obj obj : pta.getPointsToSet(arrayAccess.getBase())) {
                    ans = meetValue(ans, arrayValueMap.getOrDefault(new Pair<>(obj, index), Value.getUndef()));
                    ans = meetValue(ans, arrayValueMap.getOrDefault(new Pair<>(obj, Value.getNAC()), Value.getUndef()));
                }
            } else if (index.isNAC()) {
                for (Obj obj : pta.getPointsToSet(arrayAccess.getBase())) {
                    for (Map.Entry<Pair<Obj, Value>, Value> entry : arrayValueMap.entrySet()) {
                        Pair<Obj, Value> accessPair = entry.getKey();
                        if (accessPair.getO1().equals(obj)) {
                            ans = meetValue(ans, entry.getValue());
                        }
                    }
                }
            }
        } else ans = Value.getNAC();
        return ans;
    }
}
