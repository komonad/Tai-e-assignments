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
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Stream;

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

    public Obj getTaintObject(Invoke invoke, Type ty) {
        return manager.makeTaint(invoke, ty);
    }

    public boolean isTaintObject(Obj obj) {
        return manager.isTaint(obj);
    }

    public Set<TaintTransfer> getTaintTransfers() {
        return config.getTransfers();
    }

    public Stream<Integer> getSinksOf(JMethod method) {
        return config.getSinks().stream().filter(x -> x.method().equals(method)).map(Sink::index);
    }

    public Stream<CSObj> getSourcesOf(JMethod method, Invoke invoke) {
        return config.getSources().stream().filter(x -> x.method().equals(method)).map(Source::type)
            .map(x -> manager.makeTaint(invoke, x))
            .map(x -> solver.getCSManager().getCSObj(
                emptyContext,
                x
            ));
    }

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    public void taintTransfer(Context context, Invoke invoke, CSVar recv, JMethod method) {
        config.getTransfers().stream().filter(x -> x.method().equals(method))
            .forEach(transfer -> {
                baseToResult(context, invoke, recv, transfer);
                argToBase(context, invoke, recv, transfer);
                argToResult(context, invoke, transfer);
            });
    }

    public void taintTransfer(Context context, Invoke invoke, JMethod method) {
        config.getTransfers().stream().filter(x -> x.method().equals(method))
                .forEach(transfer -> {
                    argToResult(context, invoke, transfer);
                });
    }

    private void baseToResult(Context context, Invoke invoke, CSVar recv, TaintTransfer transfer) {
        if (transfer.from() == TaintTransfer.BASE && transfer.to() == TaintTransfer.RESULT) {
            recv.getPointsToSet().forEach(x -> {
                if (manager.isTaint(x.getObject())) {
                    solver.addToWorkList(csManager.getCSVar(context, invoke.getLValue()),
                        PointsToSetFactory.make(csManager.getCSObj(emptyContext,
                            manager.makeTaint(manager.getSourceCall(x.getObject()), transfer.type()))));
                }
            });
        }
    }

    private void argToBase(Context context, Invoke invoke, CSVar recv, TaintTransfer transfer) {
        if (transfer.to() == TaintTransfer.BASE && transfer.from() >= 0) {
            csManager.getCSVar(context, invoke.getInvokeExp().getArg(transfer.from()))
                .getPointsToSet().forEach(x -> {
                    if (manager.isTaint(x.getObject())) {
                        solver.addToWorkList(recv, PointsToSetFactory.make(csManager.getCSObj(emptyContext,
                            manager.makeTaint(manager.getSourceCall(x.getObject()), transfer.type()))));
                    }
                });
        }
    }

    private void argToResult(Context context, Invoke invoke, TaintTransfer transfer) {
        if (transfer.to() == TaintTransfer.RESULT && transfer.from() >= 0) {
            csManager.getCSVar(context, invoke.getInvokeExp().getArg(transfer.from()))
                .getPointsToSet().forEach(x -> {
                    if (manager.isTaint(x.getObject())) {
                        solver.addToWorkList(csManager.getCSVar(context, invoke.getLValue()),
                            PointsToSetFactory.make(csManager.getCSObj(emptyContext, manager.makeTaint(
                                manager.getSourceCall(x.getObject()), transfer.type())))
                        );
                    }
                });
        }
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        var cg = result.getCSCallGraph();

        cg.edges().forEach(edge -> {
            var context = edge.getCallSite().getContext();
            var invoke = edge.getCallSite().getCallSite();
            var method = edge.getCallee().getMethod();
            getSinksOf(method).forEach(i -> {
                result.getPointsToSet(csManager.getCSVar(context, invoke.getInvokeExp().getArg(i)))
                    .forEach(obj -> {
                        if (manager.isTaint(obj.getObject())) {
                            taintFlows.add(new TaintFlow(manager.getSourceCall(obj.getObject()), invoke, i));
                        }
                    });
            });
        });

        return taintFlows;
    }
}
