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

import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.heap.MockObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.util.InvokeUtils;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;

import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Handles sources in taint analysis.
 */
public class SourceHandler extends OnFlyHandler {

    /**
     * Map from a source method to its result sources.
     */
    private final MultiMap<JMethod, CallSource> callSources = Maps.newMultiMap();

    /**
     * Map from a method to {@link Invoke} statements in the method
     * which matches any call source.
     * This map matters only when call-site mode is enabled.
     */
    private final MultiMap<JMethod, Invoke> callSiteSources = Maps.newMultiMap();

    /**
     * Map from a source method to its parameter sources.
     */
    private final MultiMap<JMethod, ParamSource> paramSources = Maps.newMultiMap();

    private record SourceInfo(IndexRef indexRef, Obj taint) {
    }

    private final MultiMap<Var, SourceInfo> sourceInfos = Maps.newMultiMap();

    /**
     * Whether this handler needs to handle field sources.
     */
    private final boolean handleFieldSources;

    /**
     * Map from a source field taint objects generated from it.
     */
    private final Map<JField, Type> fieldSources = Maps.newMap();

    /**
     * Maps from a method to {@link LoadField} statements in the method
     * which loads a source field.
     */
    private final MultiMap<JMethod, LoadField> loadedFieldSources = Maps.newMultiMap();

    SourceHandler(HandlerContext context) {
        super(context);
        context.config().sources().forEach(src -> {
            if (src instanceof CallSource callSrc) {
                callSources.put(callSrc.method(), callSrc);
            } else if (src instanceof ParamSource paramSrc) {
                paramSources.put(paramSrc.method(), paramSrc);
            } else if (src instanceof FieldSource fieldSrc) {
                fieldSources.put(fieldSrc.field(), fieldSrc.type());
            }
        });
        handleFieldSources = !fieldSources.isEmpty();
    }

    /**
     * Handles call sources.
     */
    @Override
    public void onNewCallEdge(Edge<CSCallSite, CSMethod> edge) {
        if (edge.getKind() == CallKind.OTHER) {
            return;
        }
        // 如果callee的方法为source——res映射（根据配置得出所有产生tain的方法,从而产生相应的taint
        Set<CallSource> sources = callSources.get(edge.getCallee().getMethod());
        if (!sources.isEmpty()) {
            Context context = edge.getCallSite().getContext();
            Invoke callSite = edge.getCallSite().getCallSite();
            sources.forEach(source -> processCallSource(context, callSite, source));
        }

    }

//    // 判断五种条件，来决定该invoke是否需要探查:返回true说明需要探查,false不需要探查
//    @Override
//    public boolean judgeCheck(Edge<CSCallSite, CSMethod> edge,CSVar csVar) {
//        JMethod method = edge.getCallee().getMethod();
//        Context context = edge.getCallSite().getContext();
//        Invoke callSite = edge.getCallSite().getCallSite();
//        // 1. 判断pts(recv)是否包含taint
//        boolean taintOfVarFlag = true;
//        for (CSObj recvObj : solver.getPointsToSetOf(csVar)) {
//            Obj obj = recvObj.getObject();
//            MockObj taint = (MockObj) obj;
//            if (taint.getDescriptor().string().equals("TaintObj")) {
//                taintOfVarFlag = false;
//                break;
//            }
//        }
//        // 2.判断pts(argu)是否包含taint
//        InvokeExp invokeExp = callSite.getInvokeExp();
//        List<Var> args = invokeExp.getArgs();
//        boolean taintOfArgFlag = true;
//        for(Var arg: args){
//            for (CSObj csObj : solver.getPointsToSetOf(csManager.getCSVar(context,arg))) {
//                Obj obj = csObj.getObject();
//                MockObj taint = (MockObj) obj;
//                if (taint.getDescriptor().string().equals("TaintObj")) {
//                    taintOfArgFlag = false;
//                    break;
//                }
//            }
//            if(!taintOfArgFlag) break;
//        }
//
//        // 3. 判断是否为Callsource,是则传播<recv,taint>,使得pts<recv>包含taint
//        // 这是原来sourcehandler插件的onNewCallEdge方法
//        boolean taintOfCallFlag = true;
//        if (!(edge.getKind() == CallKind.OTHER)) {
//            Set<CallSource> sources = callSources.get(edge.getCallee().getMethod());
//            if (!sources.isEmpty()) {
//                taintOfCallFlag = false;
//                sources.forEach(source -> CallSourceAndPropagate(context, callSite, source));
//            }
//        }
//
//        // 4. 判断是否为paramsource,是则传播<param,taint>,使得pts<param>包含taint
//        // OnNewCSMethod方法下的handleparamSource
//        boolean taintOfParamFlag = true;
//        if (paramSources.containsKey(method)) {
//            taintOfParamFlag = false;
//            IR ir = method.getIR();
//            paramSources.get(method).forEach(source -> {
//                IndexRef indexRef = source.indexRef();
//                // 获得callee的params
//                Var param = ir.getParam(indexRef.index());
//                SourcePoint sourcePoint = new ParamSourcePoint(method, indexRef);
//                Obj taint = manager.makeTaint(sourcePoint, source.type());
//                switch (indexRef.kind()) {
//                    case VAR -> {
//                        Pointer pointer = csManager.getCSVar(context, param);
//                        solver.propagate(pointer, taint);
//                    }
//                    case ARRAY, FIELD -> {
//                        SourceInfo info = new SourceInfo(indexRef, taint);
//                        Pointer csParam = csManager.getCSVar(context, param);
//                        addArrayFieldTaintNew(solver.getPointsToSetOf(csParam), info);
////                        sourceInfos.put(
////                                param, new SourceInfo(indexRef, taint));
//                    }
//                }
//            });
//        }
//
//        // 5. 判断是否该方法是否包含FieldSource
//        boolean taintOfFieldFlag = true;
//
//
//        if(taintOfVarFlag && taintOfArgFlag && taintOfCallFlag && taintOfParamFlag && taintOfFieldFlag){
//            return false;
//        }
//        return true;
//    }



    /**
     * 为调用方法生成污点并传播污点
     */
    private void CallSourceAndPropagate(Context context, Invoke callSite, CallSource source) {
        IndexRef indexRef = source.indexRef();
        int index = indexRef.index();
        if (InvokeUtils.RESULT == index && callSite.getLValue() == null) {
            return;
        }
        Var var = InvokeUtils.getVar(callSite, index);
        SourcePoint sourcePoint = new CallSourcePoint(callSite, indexRef);
        Obj taint = manager.makeTaint(sourcePoint, source.type());
        switch (indexRef.kind()) {
//            case VAR -> solver.addVarPointsTo(context, var, taint);
            case VAR -> {
                Pointer point = csManager.getCSVar(context,var);
                // PTS传播
                solver.propagate(point,taint);
//                solver.addVarPointsTo(context, var, taint);
            }
            case ARRAY, FIELD -> {
                SourceInfo info = new SourceInfo(indexRef, taint);
                sourceInfos.put(var, info);
                CSVar csVar = csManager.getCSVar(context, var);
                // PTS传播
                addArrayFieldTaintNew(solver.getPointsToSetOf(csVar), info);
            }
        }
    }



        /**
         * Generates taint objects from call sources.
         */
    private void processCallSource(Context context, Invoke callSite, CallSource source) {
        IndexRef indexRef = source.indexRef();
        int index = indexRef.index();
        if (InvokeUtils.RESULT == index && callSite.getLValue() == null) {
            return;
        }
        Var var = InvokeUtils.getVar(callSite, index);
        SourcePoint sourcePoint = new CallSourcePoint(callSite, indexRef);
        Obj taint = manager.makeTaint(sourcePoint, source.type());
        switch (indexRef.kind()) {
            case VAR -> solver.addVarPointsTo(context, var, taint);
            case ARRAY, FIELD -> {
                SourceInfo info = new SourceInfo(indexRef, taint);
                sourceInfos.put(var, info);
                CSVar csVar = csManager.getCSVar(context, var);
                addArrayFieldTaint(solver.getPointsToSetOf(csVar), info);
            }
        }
    }
    //
    private void addArrayFieldTaintNew(PointsToSet baseObjs, SourceInfo info) {
        // indexRef表示字段相关，与数组无关
        IndexRef indexRef = info.indexRef();
        Obj taint = info.taint();
        switch (indexRef.kind()) {
            //对baseObjs中的每个抽象对象调用csManager的getArrayIndex方法获得对应的数组索引arrayIndex
            // 对流中的每个数组索引，执行solver对象的propagate方法，将taint传递给arrayIndex。
            case ARRAY -> baseObjs.objects()
                    .map(csManager::getArrayIndex)
                    .forEach(arrayIndex -> solver.propagate(arrayIndex, taint));
            case FIELD -> {
                JField f = indexRef.field();
                baseObjs.objects()
                        .map(o -> csManager.getInstanceField(o, f))
                        .forEach(oDotF ->
                                solver.propagate(oDotF, taint));
            }
        }
    }
    private void addArrayFieldTaint(PointsToSet baseObjs, SourceInfo info) {
        IndexRef indexRef = info.indexRef();
        Obj taint = info.taint();
        switch (indexRef.kind()) {
            case ARRAY -> baseObjs.objects()
                    .map(csManager::getArrayIndex)
                    .forEach(arrayIndex -> solver.addPointsTo(arrayIndex, taint));
            case FIELD -> {
                JField f = indexRef.field();
                baseObjs.objects()
                        .map(o -> csManager.getInstanceField(o, f))
                        .forEach(oDotF ->
                                solver.addPointsTo(oDotF, taint));
            }
        }
    }

    @Override
    public void onNewPointsToSet(CSVar csVar, PointsToSet pts) {
        sourceInfos.get(csVar.getVar())
                .forEach(info -> addArrayFieldTaint(pts, info));
    }

    @Override
    public void onNewStmt(Stmt stmt, JMethod container,Context context) {
        if (handleFieldSources && stmt instanceof LoadField loadField) {
            // Handle field sources.
            // If a {@link LoadField} loads any source fields,
            // then records the {@link LoadField} statements.
            JField field = loadField.getFieldRef().resolveNullable();
            if (fieldSources.containsKey(field)) {
                loadedFieldSources.put(container, loadField);
            }
        }
        if (callSiteMode &&
                stmt instanceof Invoke invoke &&
                !invoke.isDynamic()) {
            // Handles call sources for the case when call-site mode is enabled.
            // If method references of any {@link Invoke}s are resolved to
            // call source method, then records the {@link Invoke} statements.
            JMethod callee = invoke.getMethodRef().resolveNullable();
            if (callSources.containsKey(callee)) {
                callSiteSources.put(container, invoke);
            }
        }
    }

    @Override
    public void onNewCSMethod(CSMethod csMethod) {
        handleParamSource(csMethod);
        if (handleFieldSources) {
            handleFieldSource(csMethod);
        }
        if (callSiteMode) {
            handleCallSource(csMethod);
        }
    }

    private void handleParamSource(CSMethod csMethod) {
        JMethod method = csMethod.getMethod();
        if (paramSources.containsKey(method)) {
            Context context = csMethod.getContext();
            IR ir = method.getIR();
            paramSources.get(method).forEach(source -> {
                IndexRef indexRef = source.indexRef();
                Var param = ir.getParam(indexRef.index());
                SourcePoint sourcePoint = new ParamSourcePoint(method, indexRef);
                Obj taint = manager.makeTaint(sourcePoint, source.type());
                switch (indexRef.kind()) {
                    case VAR -> solver.addVarPointsTo(context, param, taint);
                    case ARRAY, FIELD -> sourceInfos.put(
                            param, new SourceInfo(indexRef, taint));
                }
            });
        }
    }

    /**
     * If given method contains pre-recorded {@link LoadField} statements,
     * adds corresponding taint object to LHS of the {@link LoadField}.
     */
    private void handleFieldSource(CSMethod csMethod) {
        JMethod method = csMethod.getMethod();
        Set<LoadField> loads = loadedFieldSources.get(method);
        if (!loads.isEmpty()) {
            Context context = csMethod.getContext();
            loads.forEach(load -> {
                Var lhs = load.getLValue();
                SourcePoint sourcePoint = new FieldSourcePoint(method, load);
                JField field = load.getFieldRef().resolve();
                Type type = fieldSources.get(field);
                Obj taint = manager.makeTaint(sourcePoint, type);
                solver.addVarPointsTo(context, lhs, taint);
            });
        }
    }

    /**
     * If given method contains pre-recorded {@link Invoke} statements,
     * call {@link #processCallSource} to generate taint objects.
     */
    private void handleCallSource(CSMethod csMethod) {
        JMethod method = csMethod.getMethod();
        Set<Invoke> callSites = callSiteSources.get(method);
        if (!callSites.isEmpty()) {
            Context context = csMethod.getContext();
            callSites.forEach(callSite -> {
                JMethod callee = callSite.getMethodRef().resolve();
                callSources.get(callee).forEach(source ->
                        processCallSource(context, callSite, source));
            });
        }
    }
}
