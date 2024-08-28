package pascal.taie.analysis.pta.plugin.taint;

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

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.core.solver.Transfer;
import pascal.taie.analysis.pta.plugin.util.InvokeUtils;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.ArrayType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;

import java.util.*;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.stream.Collectors;

/**
 * Handles sources in taint analysis.
 */
public class TaintAnalysisHandler extends OnFlyHandler {
//    private final Set<JClass>  fieldContainers;

    private static final Logger logger = LogManager.getLogger(TransferHandler.class);
    /**
     * Map from a source method to its result sources.
     */
    private final MultiMap<JMethod, CallSource> callSources = Maps.newMultiMap();
    private final Set<String> callSources1 = new HashSet<>();

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
    private final Set<String> paramSources1 = new HashSet<>();

    private record SourceInfo(IndexRef indexRef, Obj taint) {
    }

    private final MultiMap<Var, SourceInfo> sourceInfos = Maps.newMultiMap();

    /**
     * Whether this handler needs to handle field sources.
     */

    /**
     * Map from a source field taint objects generated from it.
     */
    private final Map<JField, Type> fieldSources = Maps.newMap();

    /**
     * Maps from a method to {@link LoadField} statements in the method
     * which loads a source field.
     */
    private final MultiMap<JMethod, LoadField> loadedFieldSources = Maps.newMultiMap();

    /*===========================Handles taint transfers in taint analysis.=================
     * */

    private final Context emptyContext;

    /**
     * Map from method (which causes taint transfer) to set of relevant
     * {@link TaintTransfer}.
     */
    private final MultiMap<JMethod, TaintTransfer> transfers = Maps.newMultiMap();

    private final Set<String> transfersStr = new HashSet<>();

    private final Map<Type, Transfer> transferFunctions = Maps.newHybridMap();

    private enum Kind {
        VAR_TO_ARRAY, VAR_TO_FIELD, ARRAY_TO_VAR, FIELD_TO_VAR
    }

    private record TransferInfo(Kind kind, Var var, TaintTransfer transfer) {
    }

    private final MultiMap<Var, TransferInfo> transferInfos = Maps.newMultiMap();

    /**
     * Map from a method to {@link Invoke} statements in the method
     * which matches any transfer method.
     * This map matters only when call-site mode is enabled.
     */
    private final MultiMap<JMethod, Invoke> callSiteTransfers = Maps.newMultiMap();

    /**
     * Whether enable taint back propagation to handle aliases about
     * tainted mutable objects, e.g., char[].
     */
    private final boolean enableBackPropagate = true;

    /**
     * Cache statements generated for back propagation.
     */
    private final Map<Var, List<Stmt>> backPropStmts = Maps.newMap();

    /**
     * Counter for generating temporary variables.
     */
    private int counter = 0;

    private Set<JMethod> MethodsOfContainSources;
    private final Set<JMethod> MethodsOfContainFieldSource = new HashSet<>();
    private final Set<JClass> ClassOfContainSources = new HashSet<>();

    Set<String> SourcesMethondStr = new HashSet<>();

    Pair<Set<JMethod>, Set<String>> pairConfig;


    //=====================================================================

    TaintAnalysisHandler(HandlerContext context) {
        super(context);
        context.config().sources().forEach(src -> {
            if (src instanceof CallSource callSrc) {
                callSources.put(callSrc.method(), callSrc);
                callSources1.add(callSrc.method().getName());
                SourcesMethondStr.add(callSrc.method().getName());
            } else if (src instanceof ParamSource paramSrc) {
                paramSources.put(paramSrc.method(), paramSrc);
                paramSources1.add(paramSrc.method().getName());
                SourcesMethondStr.add(paramSrc.method().getName());
            } else if (src instanceof FieldSource fieldSrc) {
                fieldSources.put(fieldSrc.field(), fieldSrc.type());
            }
        });
        List<JClass> list = solver.getHierarchy().applicationClasses().toList();
        MethodCollector methodCollector = new MethodCollector(SourcesMethondStr,list,fieldSources);
        pairConfig = methodCollector.collectMethods();
        analyzeCallSources(list);
        emptyContext = solver.getContextSelector().getEmptyContext();
        context.config().transfers()
                .forEach(t -> {
                    if(t.method().getName().equals("getValue"))
                        t.method().getName();
                    this.transfers.put(t.method(), t);
                    transfersStr.add(t.method().getName());
                });

    }

    public void analyzeCallSources(List<JClass> classList) {
        classList.forEach(jClass -> jClass.getDeclaredMethods().forEach(jMethod -> {
            if (jMethod.isAbstract() || jMethod.isNative()) {
                return;
            }

            IR ir = jMethod.getIR();
            if (ir == null) {
                return;
            }

            AtomicBoolean foundInMethod = new AtomicBoolean(false);

            ir.invokes(false).forEach(invokeStmt -> {
                String calleeName = invokeStmt.getMethodRef().getName();
                if (SourcesMethondStr.contains(calleeName)) {
                    MethodsOfContainSources.add(jMethod);
                    ClassOfContainSources.add(jMethod.getDeclaringClass());
                    foundInMethod.set(true);
                }
            });

            if (foundInMethod.get()) {
                return;
            }

            ir.stmts().forEach(stmt -> {
                if (stmt instanceof LoadField loadFieldStmt) {
                    JField field = loadFieldStmt.getFieldRef().resolve();
                    Type type = fieldSources.get(field);
                    if (type != null) {
                        MethodsOfContainFieldSource.add(jMethod);
                        ClassOfContainSources.add(jMethod.getDeclaringClass());
                        foundInMethod.set(true);
                    }
                }
            });
        }));
    }


    @Override
    public boolean judgeCallSource(Edge<CSCallSite, CSMethod> edge, AtomicBoolean flagInit) {
        JMethod method = edge.getCallee().getMethod();
        Invoke callSite = edge.getCallSite().getCallSite();
//        AtomicBoolean flag = new AtomicBoolean(false);
        AtomicBoolean f = new AtomicBoolean(true);
        if (!(edge.getKind() == CallKind.OTHER)) {
            Set<CallSource> sources = callSources.get(method);
            if (!sources.isEmpty()) {
                f.set(true);
            } else if (callSources1.contains(method.getName())) {
                List<JMethod> tmpMethod = callSources.keySet().stream().filter(a -> a.getName().equals(method.getName())).toList();
                List<CallSource> callSourceList = new ArrayList<>();
                callSources.get(tmpMethod.get(0)).forEach(source -> {
                    IndexRef indexRef = source.indexRef();
                    Var var = InvokeUtils.getVar(callSite, indexRef.index());
                    if (var != null) {
                        CallSource cs = new CallSource(tmpMethod.get(0), source.indexRef(), var.getType());
                        callSourceList.add(cs);
                    }
                });
                if (!callSourceList.isEmpty()) {
                    callSourceList.forEach(cs -> callSources.put(method, cs));
                    f.set(true);
                }
            }

        }
        if(!flagInit.get())
            flagInit.set(f.get());
        return f.get();

    }

    @Override
    public void TransferCallSource(Edge<CSCallSite, CSMethod> edge){
        JMethod method = edge.getCallee().getMethod();
        Context context = edge.getCallSite().getContext();
        Invoke callSite = edge.getCallSite().getCallSite();
        callSources.get(method).forEach(source -> CallSourceAndPropagate(context, callSite, source));

    }


    private boolean checkPointsToSetForTaint(PointsToSet pts) {
        for (CSObj csObj : pts) {
            if (manager.isTaint(csObj.getObject())) {
                return true;
            }
        }
        return false;
    }

    @Override
    public boolean judgeCheck(Edge<CSCallSite, CSMethod> edge, CSVar csVar, AtomicBoolean flagInit) {

        JMethod method = edge.getCallee().getMethod();
        Context context = edge.getCallSite().getContext();
        Invoke callSite = edge.getCallSite().getCallSite();

        // 判断该方法是否包含taint-config中方法的调用语句或者field复制语句,存在则探查
        // 以及判断该方法所在语句的所在方法是否属于 1. 存在source的方法 2. 存在source被调用链上
        boolean taintOfConfigFlag = pairConfig.methodsStrOfSourcesContainer().contains(method.getName()) || pairConfig.methodsOfContainSources().contains(method);
        //  传入的flagInit判断该所被调用的方法是否需要探查(transfer除外)
        // 如果该方法所在语句属于1. 存在source的方法 或者 2. 存在source被调用链上,即使没有污点传入和产生,也设置为true
        if (!flagInit.get() && taintOfConfigFlag)
            flagInit.set(true);
        // 1. 判断pts(recv)是否包含taint
        boolean taintOfVarFlag = false;
        if (csVar != null)
            for (CSObj recvObj : solver.getPointsToSetOf(csVar)) {
                taintOfVarFlag = manager.isTaint(recvObj.getObject());
                if (taintOfVarFlag) {
                    break;
                }
            }

        // 2.判断pts(argu)是否包含taint
        InvokeExp invokeExp = callSite.getInvokeExp();
        List<Var> args = invokeExp.getArgs();
        boolean taintOfArgFlag = false;
        for (Var arg : args) {
            for (CSObj csObj : solver.getPointsToSetOf(csManager.getCSVar(context, arg))) {
                if (manager.isTaint(csObj.getObject())) {
                    taintOfArgFlag = true;
                    break;
                }
            }
            if (taintOfArgFlag) break;
        }

        // 处理不同对象类型的变量之间的污点传播
        //   获取被调用方法的污点转移集合 tfs
        // 目前策略:当callee为transfer方法时,不探究方法内部
        // 后续: 当前策略会导致lhs的obj类型不精确,后续lhs调用方法时无法找到正确的callee,考虑继续探查
        if(transfers.get(method).isEmpty() && transfersStr.contains(method.getName())){
            List<JMethod> tmpMethod = transfers.keySet().stream().filter(a -> a.getName().equals(method.getName())).toList();
            List<JClass> tmpClass = tmpMethod.stream().map(JMethod::getDeclaringClass).toList();
            tmpMethod.forEach(m -> {
                JClass jClass = method.getDeclaringClass();
                boolean f2 = false;
                if(m.getParamCount()==method.getParamCount()){
                    while (jClass != null && !jClass.getName().equals("java.lang.Object")) {
                        if (tmpClass.contains(jClass)) {
                            f2 = true;
                        }
                        // 检查 jClass 的所有父接口
                        for (JClass superInterface : jClass.getInterfaces()) {
                            if (tmpClass.contains(superInterface)) {
                                f2 = true;
                                break; // 如果找到，立即退出循环
                            }
                        }

                        jClass = jClass.getSuperClass();
                    }
                    if(f2){
                        List<TaintTransfer> taintTransfersList = new ArrayList<>();
                        transfers.get(m).forEach(tf ->{
                            IndexRef fromRef = tf.from();
                            IndexRef toRef = tf.to();
                            Var var = InvokeUtils.getVar(callSite,toRef.index());
                            if(var!=null){
                                TaintTransfer taintTransfer = new TaintTransfer(tmpMethod.get(0), fromRef, toRef, var.getType());
                                taintTransfersList.add(taintTransfer);
                            }
                        });
                        if(!taintTransfersList.isEmpty()){
                            taintTransfersList.forEach(tf -> transfers.put(method,tf));
                        }
                    }
                }

            });


        }
        Set<TaintTransfer> tfs = transfers.get(method);
        if(!tfs.isEmpty()){
            // 3. 当已确认args或var存在污点,
            // 那么返回导致var或return(lhs)存在污点,
            if (taintOfVarFlag || taintOfArgFlag) {
                //  如果调用边的类型是 CallKind.OTHER（例如反射调用），当前不处理这些调用边，直接返回。
                if (edge.getKind() == CallKind.OTHER) {
                    return flagInit.get();
                }
                tfs.forEach(tf -> processTransfer(context, callSite, tf));
                // 这种传播类函数的内部内容不需要探究
//                return flagInit.get();
            }
            // 为transfer非静态方法方法但没有污点,正常传播: base->result
            // 这里假设所有transfer方法的result和base是同一类型
//            else if (csVar != null && lhs != null) {
//                // pass results to LHS variable
//                CSVar to = csManager.getCSVar(context, lhs);
//                solver.propagateNew(to, solver.getPointsToSetOf(csVar));
//            }
        }


        // 4. 判断方法本身所在invoke语句是否为paramsource,是则传播<param,taint>,使得pts<param>包含taint
        // OnNewCSMethod方法下的handleparamSource
        // 可能source为接口方法,传入的method为实现类的重写方法,导致不一致,需要考虑
        boolean taintOfParamFlag = false;
        IR ir = method.getIR();
        Set<JMethod> tmp = new HashSet<>();
        if (paramSources.containsKey(method)) {
            taintOfParamFlag = true;
            tmp.add(method);
        } else if (paramSources1.contains(method.getName())) {
            taintOfParamFlag = true;
            List<JMethod> tmpMethod = paramSources.keySet().stream().filter(a -> a.getName().equals(method.getName())).toList();
            List<ParamSource> paramSourceList = new ArrayList<>();
            tmpMethod.forEach(tmpM ->{
                if(tmpM.getParamCount()==method.getParamCount()){
                    paramSources.get(tmpM).forEach(source -> {
                        IndexRef indexRef = source.indexRef();
                        Var param = ir.getParam(indexRef.index());
                        ParamSource ps = new ParamSource(tmpMethod.get(0), source.indexRef(), param.getType());
                        paramSourceList.add(ps);
                    });
                    paramSourceList.forEach(ps -> paramSources.put(method, ps));
                }
            });

        }
        if (taintOfParamFlag) {
            paramSources.get(method).forEach(source -> {
                IndexRef indexRef = source.indexRef();
                // 获得callee的params
                Var param = ir.getParam(indexRef.index());
                SourcePoint sourcePoint = new ParamSourcePoint(method, indexRef);
                switch (indexRef.kind()) {
                    case VAR -> {
                        Obj taint = manager.makeTaint(sourcePoint, source.type());
                        Pointer pointer = csManager.getCSVar(context, param);
                        solver.propagateNew(pointer, taint);
                    }
                    case ARRAY -> {
                        Pointer csParam = csManager.getCSVar(context, param);
                        // gai:array
                        PointsToSet pts = solver.getPtsArrayElems(csParam);
                        if(!pts.isEmpty()){
                            Type type =  pts.iterator().next().getObject().getType();
                            Obj taint = manager.makeTaint(sourcePoint, type);
                            SourceInfo info = new SourceInfo(indexRef, taint);
                            addArrayFieldTaintNew(pts, info);
                        }

                    }
                    case FIELD -> {
                        Obj taint = manager.makeTaint(sourcePoint, source.type());
                        SourceInfo info = new SourceInfo(indexRef, taint);
                        Pointer csParam = csManager.getCSVar(context, param);
                        PointsToSet pts = solver.getPointsToSetOf(csParam);
                        if (pts.isEmpty())
                            pts.addObject(csManager.getCSObj(context, taint));
                        addArrayFieldTaintNew(pts, info);

                    }
                }
            });
        }

        if(taintOfVarFlag || taintOfArgFlag || taintOfParamFlag || taintOfConfigFlag)
            return true;
        else
            return flagInit.get();

    }

    /**
     * 为调用方法生成污点并传播污点
     */
    private void CallSourceAndPropagate(Context context, Invoke callSite, CallSource source) {
        IndexRef indexRef = source.indexRef();
        int index = indexRef.index();
        if (InvokeUtils.RESULT == index && callSite.getLValue() == null) {
            return ;
        }
        Var var = InvokeUtils.getVar(callSite, index);
        SourcePoint sourcePoint = new CallSourcePoint(callSite, indexRef);
        switch (indexRef.kind()) {
//            case VAR -> solver.addVarPointsTo(context, var, taint);
            case VAR -> {
                Obj taint = manager.makeTaint(sourcePoint, source.type());
                Pointer point = csManager.getCSVar(context, var);
                // PTS传播
                solver.propagateNew(point, taint);
//                solver.addVarPointsTo(context, var, taint);
            }
            case ARRAY -> {

                CSVar csVar = csManager.getCSVar(context, var);
                // gai:array
                PointsToSet pts = solver.getPtsArrayElems(csVar);
                if (!pts.isEmpty()) {
                    Type type = pts.iterator().next().getObject().getType();
                    Obj taint = manager.makeTaint(sourcePoint, type);
                    SourceInfo info = new SourceInfo(indexRef, taint);
                    sourceInfos.put(var, info);
                    // PTS传播
                    addArrayFieldTaintNew(pts, info);
                }


            }
            case FIELD -> {
                Obj taint = manager.makeTaint(sourcePoint, source.type());
                SourceInfo info = new SourceInfo(indexRef, taint);
                sourceInfos.put(var, info);
                CSVar csVar = csManager.getCSVar(context, var);
                PointsToSet pts = solver.getPointsToSetOf(csVar);
                if (pts.isEmpty())
                    pts.addObject(csManager.getCSObj(context, taint));

                // PTS传播
                addArrayFieldTaintNew(pts, info);
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
            case ARRAY -> baseObjs.objects().forEach(o ->{
                if(o.getObject().getType() instanceof  ArrayType){
                    solver.propagateNew(csManager.getArrayIndex(o),taint);
                }
                else {
                    Var var = (Var) o.getObject().getAllocation();
                    solver.propagateNew(csManager.getCSVar(o.getContext(),var),taint);
                }
            });
            case FIELD -> {
                JField f = indexRef.field();
                baseObjs.objects()
                        .map(o -> csManager.getInstanceField(o, f))
                        .forEach(oDotF ->
                                solver.propagateNew(oDotF, taint));
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

    //==================transfer=======================
    private void processTransfer(Context context, Invoke callSite, TaintTransfer transfer) {
        IndexRef from = transfer.from();
        IndexRef to = transfer.to();
        Var toVar = InvokeUtils.getVar(callSite, to.index());
        if (toVar == null) {
            return;
        }
        Var fromVar = InvokeUtils.getVar(callSite, from.index());
        CSVar csFrom = csManager.getCSVar(context, fromVar);
        CSVar csTo = csManager.getCSVar(context, toVar);
        if (from.kind() == IndexRef.Kind.VAR) { // Var -> Var/Array/Field
            Kind kind = switch (to.kind()) {
                case VAR -> {
                    Transfer tf = getTransferFunction(transfer.type());
//                    获取 转移函数 tf 并在求解器 solver 中添加污点转移边 TaintTransferEdge。
                    solver.addPFGEdgeAndPropagate(
                            new TaintTransferEdge(csFrom, csTo),
                            tf);
                    yield null;
                }
                case ARRAY -> Kind.VAR_TO_ARRAY;
                case FIELD -> Kind.VAR_TO_FIELD;
            };
//            目标 to 是数组或字段，创建 TransferInfo 对象并存储在 transferInfos 中，然后调用 transferTaint 方法进行污点转移
            if (kind != null) {
                TransferInfo info = new TransferInfo(kind, fromVar, transfer);
                transferInfos.put(toVar, info);
                // gai:array
                PointsToSet pts;
                if(solver.isContainedArray(csTo)){
                    pts = solver.getPtsArrayElems(csTo);
                }
                else {
                    pts = solver.getPointsToSetOf(csTo);
                }
//                if(pts.isEmpty()){
//                    pts = solver.getPtsArrayElems(csTo);
//                }
                transferTaint(pts,context, info);
            }
        } else if (to.kind() == IndexRef.Kind.VAR) { // Array/Field -> Var
            Kind kind = switch (from.kind()) {
                case ARRAY -> Kind.ARRAY_TO_VAR;
                case FIELD -> Kind.FIELD_TO_VAR;
                default -> throw new AnalysisException(); // unreachable
            };
//            根据源的类型（数组或字段），创建 TransferInfo 对象并存储在 transferInfos 中，然后调用 transferTaint 方法进行污点转移。
            TransferInfo info = new TransferInfo(kind, toVar, transfer);
            transferInfos.put(fromVar, info);
            // gai:array
            PointsToSet pts;
            if(solver.isContainedArray(csFrom)){
                pts = solver.getPtsArrayElems(csFrom);
            }
            else {
                pts = solver.getPointsToSetOf(csFrom);
            }
            transferTaint(pts, context, info);
        } else { // ignore other cases
            logger.warn("TaintTransfer {} -> {} (in {}) is not supported",
                    transfer, from.kind(), to.kind());
        }

        // If the taint is transferred to base or argument, it means
        // that the objects pointed to by "to" were mutated
        // by the invocation. For such cases, we need to propagate the
        // taint to the pointers aliased with "to". The pointers
        // whose objects come from "to" will be naturally handled by
        // pointer analysis, and we just need to specially handle the
        // pointers whose objects flow to "to", i.e., back propagation.
//        如果启用了反向传播 enableBackPropagate 且满足特定条件，调用 backPropagateTaint 方法进行污点反向传播。
        if (enableBackPropagate
                && to.index() != InvokeUtils.RESULT
                && to.kind() == IndexRef.Kind.VAR
                && !(to.index() == InvokeUtils.BASE
                && transfer.method().isConstructor())) {
            backPropagateTaint(toVar, context);
        }
    }

    /*    根据 TransferInfo 的类型，将污点转移添加到求解器 solver 中：
        VAR_TO_ARRAY：变量转移到数组。
        VAR_TO_FIELD：变量转移到字段。
        ARRAY_TO_VAR：数组转移到变量。
        FIELD_TO_VAR：字段转移到变量。*/
    //transferTaint(solver.getPointsToSetOf(csFrom), context, info);
    private void transferTaint(PointsToSet baseObjs, Context ctx, TransferInfo info) {
        CSVar csVar = csManager.getCSVar(ctx, info.var());
        Transfer tf = getTransferFunction(info.transfer().type());
//        将污点转移添加到求解器 solver 中
        switch (info.kind()) {
//            VAR_TO_ARRAY：变量转移到数组。
            case VAR_TO_ARRAY -> {
                baseObjs.objects().forEach(o -> {
                    if(o.getObject().getType() instanceof ArrayType){
                        solver.addPFGEdgeAndPropagate(
                                new TaintTransferEdge(csVar,csManager.getArrayIndex(o)),
                                tf);
                    }
                    else {
                        Var var = (Var) o.getObject().getAllocation();
                        solver.addPFGEdgeAndPropagate(
                                new TaintTransferEdge(csVar,csManager.getCSVar(o.getContext(),var)),
                                tf);
                    }
                });
            }
            case VAR_TO_FIELD -> {
                JField f = info.transfer().to().field();
                baseObjs.objects()
                        .map(o -> csManager.getInstanceField(o, f))
                        .forEach(oDotF ->
                                solver.addPFGEdgeAndPropagate(
                                        new TaintTransferEdge(csVar, oDotF),
                                        tf));
            }
            case ARRAY_TO_VAR -> {
//                baseObjs.objects()
//                        .map(csManager::getArrayIndex)
//                        .forEach(arrayIndex ->
//                                solver.addPFGEdgeAndPropagate(
//                                        new TaintTransferEdge(arrayIndex, csVar),
//                                        tf));

                baseObjs.objects().forEach(o -> {
                    if(o.getObject().getType() instanceof ArrayType){
                        solver.addPFGEdgeAndPropagate(
                                new TaintTransferEdge(csManager.getArrayIndex(o), csVar),
                                tf);
                    }
                    else {
                        Var var = (Var) o.getObject().getAllocation();
                        solver.addPFGEdgeAndPropagate(
                                new TaintTransferEdge(csManager.getCSVar(o.getContext(),var), csVar),
                                tf);
                    }
                });

            }
            case FIELD_TO_VAR -> {
                JField f = info.transfer().from().field();
                baseObjs.objects()
                        .map(o -> csManager.getInstanceField(o, f))
                        .forEach(oDotF ->
                                solver.addPFGEdgeAndPropagate(
                                        new TaintTransferEdge(oDotF, csVar),
                                        tf));
            }
        }
    }

    private Transfer getTransferFunction(Type toType) {
//        computeIfAbsent 方法的作用是，如果 toType 对应的值不存在，则计算一个新的值并存储在 Map 中，否则返回已存在的值。
        return transferFunctions.computeIfAbsent(toType,
                type -> ((edge, input) -> { // / 这里的 lambda 表达式定义了一个 Transfer 对象
                    PointsToSet newTaints = solver.makePointsToSet(); //// 创建一个新的 PointsToSet 对象来存储新传播的污点
                    input.objects()  // 遍历输入的 PointsToSet 对象
                            .map(CSObj::getObject)  // 映射到 CSObj 对象
                            .filter(manager::isTaint)// 过滤出污点对象
                            .map(manager::getSourcePoint)   // 获取污点source
                            .map(source -> manager.makeTaint(source, type))  // 创建新的污点对象
                            .map(taint -> csManager.getCSObj(emptyContext, taint))  // 获取上下文敏感的污点对象
                            .forEach(newTaints::addObject); // 将新的污点对象添加到 newTaints 中
                    return newTaints;  // 返回新的污点集合
                }));
    }

    private void backPropagateTaint(Var to, Context ctx) {
        CSMethod csMethod = csManager.getCSMethod(ctx, to.getMethod());
        solver.addStmts(csMethod,
                backPropStmts.computeIfAbsent(to, this::getBackPropagateStmts));
    }

    private List<Stmt> getBackPropagateStmts(Var var) {
        // Currently, we handle one case, i.e., var = base.field where
        // var is tainted, and we back propagate taint from var to base.field.
        // For simplicity, we add artificial statement like base.field = var
        // for back propagation.
        JMethod container = var.getMethod();
        List<Stmt> stmts = new ArrayList<>();
        container.getIR().forEach(stmt -> {
            if (stmt instanceof LoadField load) {
                FieldAccess fieldAccess = load.getFieldAccess();
                if (fieldAccess instanceof InstanceFieldAccess ifa) {
                    // found var = base.field;
                    Var base = ifa.getBase();
                    // generate a temp base to avoid polluting original base
                    Var taintBase = getTempVar(container, base.getType());
                    stmts.add(new Copy(taintBase, base)); // %taint-temp = base;
                    // generate field store statements to back propagate taint
                    Var from;
                    Type fieldType = ifa.getType();
                    // since var may point to the objects that are not from
                    // base.field, we use type to filter some spurious objects
                    if (fieldType.equals(var.getType())) {
                        from = var;
                    } else {
                        Var tempFrom = getTempVar(container, fieldType);
                        stmts.add(new Cast(tempFrom, new CastExp(var, fieldType)));
                        from = tempFrom;
                    }
                    // back propagate taint from var to base.field
                    stmts.add(new StoreField(
                            new InstanceFieldAccess(ifa.getFieldRef(), taintBase),
                            from)); // %taint-temp.field = from;
                }
            }
        });
        return stmts.isEmpty() ? List.of() : stmts;
    }

    private Var getTempVar(JMethod container, Type type) {
        String varName = "%taint-temp-" + counter++;
        return new Var(container, varName, type, -1);
    }

}

    //========================================================


