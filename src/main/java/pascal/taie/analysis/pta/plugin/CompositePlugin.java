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
/*
 * EffiTaint: A Static Taint Analysis Tool Based on Tai-e
 *
 * Copyright (C) 2024 [Li Haocheng] <[ishaocheng@163.com]>
 *
 * Modifications in this file are part of the EffiTaint project,
 * which is based on Tai-e. These modifications are licensed under
 * the same terms as Tai-e, the GNU Lesser General Public License v3.0.
 */
package pascal.taie.analysis.pta.plugin;

import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.analysis.pta.plugin.reflection.ReflectionAnalysis;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;

import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.concurrent.atomic.AtomicBoolean;

/**
 * Composite plugin which allows multiple independent plugins
 * to be used together.
 */
public class CompositePlugin implements Plugin {

    private final List<Plugin> allPlugins = new ArrayList<>();

    // Use separate lists to store plugins that overwrite
    // frequently-invoked methods.

    private final List<Plugin> onNewPointsToSetPlugins = new ArrayList<>();

    private final List<Plugin> onNewCallEdgePlugins = new ArrayList<>();

    private final List<Plugin> onNewMethodPlugins = new ArrayList<>();

    private final List<Plugin> onNewStmtPlugins = new ArrayList<>();

    private final List<Plugin> onNewCSMethodPlugins = new ArrayList<>();

    private final List<Plugin> onUnresolvedCallPlugins = new ArrayList<>();

    private final List<Plugin> judgeCheck = new ArrayList<>();

    private final List<Plugin> judgeCallSource = new ArrayList<>();

    private final List<Plugin> TransferCallSource = new ArrayList<>();

    private final List<Plugin> ReflectionHandler = new ArrayList<>();

    public void addPlugin(Plugin... plugins) {
        for (Plugin plugin : plugins) {
            allPlugins.add(plugin);
            addPlugin(plugin, onNewPointsToSetPlugins,
                    "onNewPointsToSet", CSVar.class, PointsToSet.class);
            addPlugin(plugin, onNewCallEdgePlugins, "onNewCallEdge", Edge.class);
            addPlugin(plugin, onNewMethodPlugins, "onNewMethod", JMethod.class);
            addPlugin(plugin, onNewStmtPlugins, "onNewStmt", Stmt.class, JMethod.class,Context.class);
            addPlugin(plugin, onNewCSMethodPlugins, "onNewCSMethod", CSMethod.class);
            addPlugin(plugin, onUnresolvedCallPlugins,
                    "onUnresolvedCall", CSObj.class, Context.class, Invoke.class);
            addPlugin(plugin, judgeCheck, "judgeCheck", Edge.class,CSVar.class, AtomicBoolean.class);
            addPlugin(plugin, judgeCallSource, "judgeCallSource", Edge.class, AtomicBoolean.class);
            addPlugin(plugin, TransferCallSource, "TransferCallSource", Edge.class);
            addPlugin(plugin, ReflectionHandler, "reflectionHandler", CSMethod.class,Invoke.class);
        }
    }
    //插件是否覆盖了特定的方法，并将其添加到相应的列表中：
    private void addPlugin(Plugin plugin, List<Plugin> plugins,
                           String name, Class<?>... parameterTypes) {
        try {
            if((plugin.getClass().getName().equals("pascal.taie.analysis.pta.plugin.taint.TaintAnalysisHandler")|| plugin.getClass().getName().equals("pascal.taie.analysis.pta.plugin.taint.TaintAnalysis"))) {
                if (Objects.equals(name, "judgeCheck") || Objects.equals(name, "judgeCallSource") || Objects.equals(name, "TransferCallSource"))
                    plugins.add(plugin);
            } else {
                Method method = plugin.getClass().getMethod(name, parameterTypes);
                if (!method.getDeclaringClass().equals(Plugin.class) && !Objects.equals(name, "judgeCheck") && !Objects.equals(name, "judgeCallSource") && !Objects.equals(name, "TransferCallSource") && !Objects.equals(name, "reflectionHandler")) {
                    // the plugin does overwrite the specific method
                    plugins.add(plugin);
                }
                if(!method.getDeclaringClass().equals(Plugin.class) && Objects.equals(name, "reflectionHandler"))
                    plugins.add(plugin);
//                else if(!method.getDeclaringClass().equals(Plugin.class))
//                    plugins.add(plugin);

            }
        } catch (NoSuchMethodException e) {
//            throw new RuntimeException("Can't find method '" + name +
//                    "' in " + plugin.getClass(), e);
        }
    }

    @Override
    public void setSolver(Solver solver) {
        allPlugins.forEach(p -> p.setSolver(solver));
    }

    @Override
    public void onStart() {
        allPlugins.forEach(Plugin::onStart);
    }

    @Override
    public void onPhaseFinish() {
        allPlugins.forEach(Plugin::onPhaseFinish);
    }

    @Override
    public void onFinish() {
        allPlugins.forEach(Plugin::onFinish);
    }

    @Override
    public void onNewPointsToSet(CSVar csVar, PointsToSet pts) {
        onNewPointsToSetPlugins.forEach(p -> p.onNewPointsToSet(csVar, pts));
    }

    @Override
    public void onNewCallEdge(Edge<CSCallSite, CSMethod> edge) {
        onNewCallEdgePlugins.forEach(p -> p.onNewCallEdge(edge));
    }

    @Override
    public void onNewMethod(JMethod method) {
        onNewMethodPlugins.forEach(p -> p.onNewMethod(method));
    }

    @Override
    public void onNewStmt(Stmt stmt, JMethod container,Context context) {
        onNewStmtPlugins.forEach(p -> p.onNewStmt(stmt, container,context));
    }

    @Override
    public void onNewCSMethod(CSMethod csMethod) {
        onNewCSMethodPlugins.forEach(p -> p.onNewCSMethod(csMethod));
    }

    @Override
    public void onUnresolvedCall(CSObj recv, Context context, Invoke invoke) {
        onUnresolvedCallPlugins.forEach(p -> p.onUnresolvedCall(recv, context, invoke));
    }

    @Override
    public boolean judgeCheck(Edge<CSCallSite, CSMethod> edge,CSVar csVar,AtomicBoolean flag) {
        return judgeCheck.get(0).judgeCheck(edge,csVar,flag);
    }

    @Override
    public boolean judgeCallSource(Edge<CSCallSite, CSMethod> edge,AtomicBoolean flag) {
        return judgeCallSource.get(0).judgeCallSource(edge,flag);
    }
    @Override
    public void TransferCallSource(Edge<CSCallSite, CSMethod> edge) {
        TransferCallSource.get(0).TransferCallSource(edge);
    }
//    @Override
//    public void reflectionHandler(CSMethod csMethod,Invoke invoke) {
//        ReflectionHandler.get(0).reflectionHandler(csMethod,invoke);
//    }

}
