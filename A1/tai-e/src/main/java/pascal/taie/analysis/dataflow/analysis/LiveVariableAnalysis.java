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

import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Stmt;

/**
 * Implementation of classic live variable analysis.
 */
public class LiveVariableAnalysis extends
        AbstractDataflowAnalysis<Stmt, SetFact<Var>> {

    public static final String ID = "livevar";

    public LiveVariableAnalysis(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return false;
    }

    @Override
    public SetFact<Var> newBoundaryFact(CFG<Stmt> cfg) {
        return new SetFact<Var>();
    }

    @Override
    public SetFact<Var> newInitialFact() {
        return new SetFact<Var>();
    }

    @Override
    public void meetInto(SetFact<Var> fact, SetFact<Var> target) {
        target.union(fact);
    }

    @Override
    public boolean transferNode(Stmt stmt, SetFact<Var> in, SetFact<Var> out) {
        boolean changed=false;

        SetFact<Var>inUpdated=new SetFact<Var>();
        inUpdated.set(out);

        if(stmt.getDef().isPresent()){
            LValue def=stmt.getDef().get();
            if(def instanceof Var)
                inUpdated.remove((Var)def);
        }
        for(RValue use:stmt.getUses()){
            if(use instanceof Var ){
                inUpdated.add((Var)use);
            }
        }

        if(!inUpdated.equals(in))
            changed=true;

        in.set(inUpdated);

        return changed;
    }
}
