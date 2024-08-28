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

import com.google.common.collect.ArrayListMultimap;
import org.checkerframework.checker.nullness.qual.Nullable;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.util.InvokeUtils;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.collection.MultiMap;
import pascal.taie.util.collection.Sets;

import java.util.Collection;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Handles sinks in taint analysis.
 */
class SinkHandler extends Handler {

    private final List<Sink> sinks;

    SinkHandler(HandlerContext context) {
        super(context);
        sinks = context.config().sinks();
    }

    Set<TaintFlow> collectTaintFlows() {
        PointerAnalysisResult result = solver.getResult();
        Set<TaintFlow> taintFlows = Sets.newOrderedSet();
// 遍历每一个 sink
        for (Sink sink : sinks) {
            // 遍历进入该 sink 的方法的所有调用边
            for (Edge<Invoke, JMethod> edge : result.getCallGraph().edgesInTo(sink.method()).collect(Collectors.toList())){
                // 只处理非 CallKind.OTHER 类型的调用边
                if (edge.getKind() != CallKind.OTHER) {
                    Invoke sinkCall = edge.getCallSite();
                    Set<TaintFlow> collectedTaintFlows = collectTaintFlows(result, sinkCall, sink);
                    taintFlows.addAll(collectedTaintFlows);
                }
            }
        }

        if (callSiteMode) {
            ArrayListMultimap<@Nullable Object, @Nullable Object> sinkMap = ArrayListMultimap.create();
            for (Sink sink : sinks) {
                sinkMap.put(sink.method(), sink);
            }

            // 遍历所有可达方法
            for (JMethod reachableMethod : result.getCallGraph().reachableMethods().collect(Collectors.toList())) {
                // 遍历每一个调用点
                if(reachableMethod.isAbstract())
                    continue;
                for (Invoke callSite : reachableMethod.getIR().invokes(false).collect(Collectors.toList())) {
                    JMethod callee = callSite.getMethodRef().resolveNullable();

                    if (callee != null) {
                        if(callee.getName().equals("println"))
                            callee.getName();

                        List<@Nullable Object> methodSinks = sinkMap.get(callee);
                        if (methodSinks != null) {
                            for (@Nullable Object sink : methodSinks) {
                                Set<TaintFlow> collectedTaintFlows = collectTaintFlows(result, callSite, (Sink) sink);
                                taintFlows.addAll(collectedTaintFlows);
                            }
                        }
                    }
                }
            }
        }
        return taintFlows;
    }

    private Set<TaintFlow> collectTaintFlows(
            PointerAnalysisResult result, Invoke sinkCall, Sink sink) {
        IndexRef indexRef = sink.indexRef();
        Var arg = InvokeUtils.getVar(sinkCall, indexRef.index());
        SinkPoint sinkPoint = new SinkPoint(sinkCall, indexRef);
        // obtain objects to check for different IndexRef.Kind
        Set<Obj> objs = switch (indexRef.kind()) {
            case VAR -> result.getPointsToSet(arg);
            case ARRAY -> result.getPointsToSet(arg, (Var) null);
            case FIELD -> result.getPointsToSet(arg, indexRef.field());
        };
        return objs.stream()
                .filter(manager::isTaint)
                .map(manager::getSourcePoint)
                .map(sourcePoint -> new TaintFlow(sourcePoint, sinkPoint))
                .collect(Collectors.toSet());
    }
}
