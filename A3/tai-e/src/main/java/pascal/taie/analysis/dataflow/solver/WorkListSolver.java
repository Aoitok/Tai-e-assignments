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

package pascal.taie.analysis.dataflow.solver;

import java.util.HashSet;
import java.util.Set;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        Set<Node> worklist = new HashSet<>();
        for (Node node : cfg) {
            if (cfg.isEntry(node)) {
                continue;
            }
            worklist.add(node);
        }
        while (!worklist.isEmpty()) {
            Set<Node> newWorklist = new HashSet<>();
            for (Node node : worklist) {
                Fact in = result.getInFact(node);
                for (Node pred : cfg.getPredsOf(node)) {
                    analysis.meetInto(result.getOutFact(pred), in);
                }
                if (analysis.transferNode(node, in, result.getOutFact(node))) {
                    for (Node succ : cfg.getSuccsOf(node)) {
                        newWorklist.add(succ);
                    }
                }
            }
            worklist = newWorklist;
        }
    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        Set<Node> worklist = new HashSet<>();
        for (Node node : cfg) {
            if (cfg.isExit(node)) {
                continue;
            }
            worklist.add(node);
        }
        while (!worklist.isEmpty()) {
            Set<Node> newWorklist = new HashSet<>();
            for (Node node : worklist) {
                Fact out = result.getOutFact(node);
                for (Node succ : cfg.getSuccsOf(node)) {
                    analysis.meetInto(result.getInFact(succ), out);
                }
                if (analysis.transferNode(node, result.getInFact(node), out)) {
                    for (Node pred : cfg.getPredsOf(node)) {
                        newWorklist.add(pred);
                    }
                }
            }
            worklist = newWorklist;
        }
    }
}
