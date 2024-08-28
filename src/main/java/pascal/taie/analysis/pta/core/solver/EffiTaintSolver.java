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


package pascal.taie.analysis.pta.core.solver;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.graph.flowgraph.FlowKind;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.Descriptor;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.MockObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.analysis.pta.plugin.taint.CallSourcePoint;
import pascal.taie.analysis.pta.plugin.taint.IndexRef;
import pascal.taie.analysis.pta.plugin.util.InvokeUtils;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.IR;
import pascal.taie.ir.IRBuildHelper;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.ArrayType;
import pascal.taie.language.type.ClassType;
import pascal.taie.language.type.Type;
import pascal.taie.language.type.TypeSystem;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.Sets;

import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.function.Predicate;
import java.util.*;

import static pascal.taie.language.classes.Signatures.FINALIZE;
import static pascal.taie.language.classes.Signatures.FINALIZER_REGISTER;

public class EffiTaintSolver implements Solver {

    private static final Logger logger = LogManager.getLogger(EffiTaintSolver.class);

    /**
     * Descriptor for array objects created implicitly by multiarray instruction.
     */
    private static final Descriptor MULTI_ARRAY_DESC = () -> "MultiArrayObj";

    private static final Descriptor ARRAY_DESC = () -> "ArrayObj";

    private static final Descriptor LHS_DESC = () -> "LhsObj";

    private static final Descriptor TAINT_DESC = () -> "TaintObj";

    /**
     * Number that represents unlimited elapsed time.
     */
    private static final long UNLIMITED = -1;

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private final CSManager csManager;

    private final ClassHierarchy hierarchy  =World.get().getClassHierarchy();

    private final TypeSystem typeSystem;

    private final PointsToSetFactory ptsFactory;

    private final PropagateTypes propTypes;

    /**
     * Whether only analyzes application code.
     */
    private final boolean onlyApp;

    /**
     * Time limit for pointer analysis (in seconds).
     */
    private final long timeLimit;

    private TimeLimiter timeLimiter;

    /**
     * Whether the analysis has reached time limit.
     */
    private volatile boolean isTimeout;

    private Plugin plugin;

    private WorkList workList;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private Set<JMethod> reachableMethods;

    /**
     * Set of classes that have been initialized.
     */
    private Set<JClass> initializedClasses;

    /**
     * Set of methods to be intercepted and ignored.
     */
    private Set<JMethod> ignoredMethods;

//    private StmtProcessor stmtProcessor;

    private PointerAnalysisResult result;




    @SuppressWarnings("unchecked")
    public EffiTaintSolver(AnalysisOptions options, HeapModel heapModel,
                           ContextSelector contextSelector, CSManager csManager) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
        this.csManager = csManager;
//        hierarchy = World.get().getClassHierarchy();
        typeSystem = World.get().getTypeSystem();
        ptsFactory = new PointsToSetFactory(csManager.getObjectIndexer());
        propTypes = new PropagateTypes(
                (List<String>) options.get("propagate-types"),
                typeSystem);
        onlyApp = options.getBoolean("only-app");
        timeLimit = options.getInt("time-limit");
    }

    private final Map<NewMultiArray, Obj[]> newArrays = Maps.newMap();

    private final Map<Pointer, CSObj[]> elementsArray = Maps.newMap();
    private final Map<Pointer, CSObj[]> elementsArray2 = Maps.newMap();

    private final Map<New, Invoke> registerInvokes = Maps.newMap();

    private final JMethod finalize = Objects.requireNonNull(
            hierarchy.getJREMethod(FINALIZE));

    private final MethodRef finalizeRef = finalize.getRef();

    private final MethodRef registerRef = Objects.requireNonNull(
            hierarchy.getJREMethod(FINALIZER_REGISTER)).getRef();

    @Override
    public AnalysisOptions getOptions() {
        return options;
    }

    @Override
    public HeapModel getHeapModel() {
        return heapModel;
    }

    @Override
    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    @Override
    public CSManager getCSManager() {
        return csManager;
    }

    @Override
    public ClassHierarchy getHierarchy() {
        return hierarchy;
    }

    @Override
    public TypeSystem getTypeSystem() {
        return typeSystem;
    }

    @Override
    public CSCallGraph getCallGraph() {
        return callGraph;
    }

    @Override
    public PointsToSet getPointsToSetOf(Pointer pointer) {
        PointsToSet pts = pointer.getPointsToSet();
        if (pts == null) {
            pts = ptsFactory.make();
            pointer.setPointsToSet(pts);
        }
        return pts;
    }

    @Override
    public PointsToSet makePointsToSet() {
        return ptsFactory.make();
    }

    @Override
    public void setPlugin(Plugin plugin) {
        this.plugin = plugin;
    }

    // ---------- solver logic starts ----------

    /**
     * Runs pointer analysis algorithm.
     */
    @Override
    public void solve() {
        initialize();
        analyze();
    }



    @Override
    public PointsToSet propagate(Pointer pointer, Obj obj) {
        return null;
    }


    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph(csManager);
        reachableMethods = Sets.newSet();
        initializedClasses = Sets.newSet();
        ignoredMethods = Sets.newSet();
        isTimeout = false;
        if (timeLimit != UNLIMITED) {
            timeLimiter = new TimeLimiter(timeLimit);
            timeLimiter.countDown();
        }
        plugin.onStart();
    }

    private class TimeLimiter {

        private static final long MILLIS_FACTOR = 1000;

        private final Thread thread;

        /**
         * @param seconds the time limit.
         */
        private TimeLimiter(long seconds) {
            thread = new Thread(() -> {
                try {
                    Thread.sleep(seconds * MILLIS_FACTOR);
                } catch (InterruptedException ignored) {
                }
                isTimeout = true;
            });
        }

        /**
         * Starts count down.
         */
        private void countDown() {
            thread.start();
        }

        /**
         * Stops count down.
         */
        private void stop() {
            thread.interrupt();
        }
    }

    /**
     * Processes work list entries until the work list is empty.
     */
    private void analyze() {

        if (timeLimiter != null) { // finish normally but time limiter is still running
            timeLimiter.stop();
        }
        plugin.onFinish();
    }



    @Override
    public void propagateNew(Pointer pointer, PointsToSet pointsToSet){

        logger.trace("Propagate {} to {}", pointsToSet, pointer);
        Set<Predicate<CSObj>> filters = pointer.getFilters();
        if (!filters.isEmpty()) {
            // apply filters (of the pointer) on pointsToSet
            pointsToSet = pointsToSet.objects()
                    .filter(o -> filters.stream().allMatch(f -> f.test(o)))
                    .collect(ptsFactory::make, PointsToSet::addObject, PointsToSet::addAll);
        }
        PointsToSet diff = getPointsToSetOf(pointer).addAllDiff(pointsToSet);
        if(pointer instanceof CSVar csVar)
            plugin.onNewPointsToSet(csVar,diff);
        if (!diff.isEmpty()) {
            pointerFlowGraph.getOutEdgesOf(pointer).stream().forEach(edge -> {
                Pointer target = edge.target();
                edge.getTransfers().stream().forEach(transfer ->
                        propagateNew(target, transfer.apply(edge, diff))
                );
            });
        }
    }




    private boolean isIgnored(JMethod method) {
        return ignoredMethods.contains(method) ||
                onlyApp && !method.isApplication();
    }

    /**
     * Processes new reachable methods.
     */
    private void processNewMethod(JMethod method) {
        if (reachableMethods.add(method)) {
            plugin.onNewMethod(method);
//            method.getIR().forEach(stmt -> plugin.onNewStmt(stmt, method));
        }
    }



    // ---------- solver logic ends ----------

    @Override
    public void addPointsTo(Pointer pointer, PointsToSet pts) {
        workList.addEntry(pointer, pts);
    }

    @Override
    public void addPointsTo(Pointer pointer, CSObj csObj) {
        PointsToSet pts = makePointsToSet();
        pts.addObject(csObj);
        addPointsTo(pointer, pts);
    }

    @Override
    public void addPointsTo(Pointer pointer, Context heapContext, Obj obj) {
        addPointsTo(pointer, csManager.getCSObj(heapContext, obj));
    }

    @Override
    public void addVarPointsTo(Context context, Var var, PointsToSet pts) {
        addPointsTo(csManager.getCSVar(context, var), pts);
    }

    @Override
    public void addVarPointsTo(Context context, Var var, CSObj csObj) {
        addPointsTo(csManager.getCSVar(context, var), csObj);
    }

    @Override
    public void addVarPointsTo(Context context, Var var, Context heapContext, Obj obj) {
        addPointsTo(csManager.getCSVar(context, var), heapContext, obj);
    }

    @Override
    public void addPointerFilter(Pointer pointer, Predicate<CSObj> filter) {
        pointer.addFilter(filter);
    }

    @Override
    public void addPFGEdge(PointerFlowEdge edge, Transfer transfer) {
        edge = pointerFlowGraph.addEdge(edge);
        if (edge != null && edge.addTransfer(transfer)) {
            PointsToSet targetSet = transfer.apply(
                    edge, getPointsToSetOf(edge.source()));
            if (!targetSet.isEmpty()) {
                addPointsTo(edge.target(), targetSet);
            }
        }
    }
    public boolean processStatement(JMethod container, Context context, Stmt stmt, ChainedIterator<Stmt> stmtIterator, Deque<VisitorState> stack, AtomicBoolean flagInit) {
        CSMethod csMethod = csManager.getCSMethod(context, container);
        processStrongUpdate(context, stmt);
        plugin.onNewStmt(stmt, container, context);

        if (stmt instanceof New) {
            return processNewStatement(container, context, (New) stmt, stmtIterator, stack, csMethod, flagInit);
        } else if (stmt instanceof LoadField) {
            processLoadFieldStatement(context, (LoadField) stmt, csMethod);
        } else if (stmt instanceof StoreField) {
            processStoreFieldStatement(context, (StoreField) stmt, csMethod);
        } else if (stmt instanceof AssignLiteral) {
            processAssignLiteralStatement(context, (AssignLiteral) stmt, csMethod);
        } else if (stmt instanceof Copy) {
            processCopyStatement(context, (Copy) stmt);
        } else if (stmt instanceof Cast) {
            processCastStatement(context, (Cast) stmt);
        } else if (stmt instanceof StoreArray) {
            processStoreArrayStatement(context, (StoreArray) stmt, csMethod);
        } else if (stmt instanceof LoadArray) {
            processLoadArrayStatement(context, (LoadArray) stmt, csMethod);
        } else if (stmt instanceof Invoke) {
            return processInvokeStatement(container, context, (Invoke) stmt, stmtIterator, stack, flagInit);
        }

        return false;
    }


    private void removeEdges(Pointer pointer){
        PointsToSet ptsLhs = getPointsToSetOf(pointer);
        if(ptsLhs.isEmpty()) return;
        // 指向集不为空
        // lhs为全新变量,消除PFG中指向和被指向对象
        // 1. 清空指向集
        pointer.setPointsToSet(makePointsToSet());
        // 2. 消除出边
        Set<PointerFlowEdge>  outEdge = new HashSet<>(pointer.getOutEdges());
        // 删除出边目标节点的各自的前驱和入边 源节点的各自的后继和出边
        if(!outEdge.isEmpty()){
            for(PointerFlowEdge edge:outEdge){
                Pointer target = edge.target();
                target.removeInEdge(edge);
//                    Pointer source = edge.target();
                // 2.2 删除当前的节点所有出边和后继者
                pointer.removeOutEdge(edge);
            }
        }
        // 3. 消除入边
        Set<PointerFlowEdge> inEdge = new HashSet<>(pointer.getInEdges());
        // 3.1 当前节点作为target,删除节点的所有前驱和入边
        if(!inEdge.isEmpty()){
            for(PointerFlowEdge edge:inEdge){
                Pointer source = edge.source();
                source.removeOutEdge(edge);
                // 3.2 删除当前的节点所有入边和前驱者
                pointer.removeInEdge(edge);
            }
        }
    }

    private void processStrongUpdate(Context context, Stmt stmt){
        //  仅处理lhs为VAR的情况
        // lhs为字段或数组时,要求左值时是一定存在字段,数组对象的
        if(stmt instanceof New || stmt instanceof AssignLiteral || stmt instanceof Cast){
            Optional<LValue> lhs = stmt.getDef();
            if(lhs.isPresent()){
                Var var = (Var) lhs.get();
                CSVar csLhs = csManager.getCSVar(context,var);
                removeEdges(csLhs);
            }

        }


    }

    private boolean processNewStatement(JMethod container, Context context, New newStmt, ChainedIterator<Stmt> stmtIterator, Deque<VisitorState> stack, CSMethod csMethod,AtomicBoolean flagInit){
        Var var = newStmt.getLValue();
        NewExp rvalue = newStmt.getRValue();
        Pointer point = csManager.getCSVar(context, var);

        // obtain context-sensitive heap object
        Obj obj = heapModel.getObj(newStmt);
        Context heapContext = contextSelector.selectHeapContext(csMethod, obj);

        PointsToSet pts = makePointsToSet();
        CSObj csObj = csManager.getCSObj(heapContext, obj);
        pts.addObject(csObj);
        propagateNew(point, pts);
        IRBuildHelper irBuildHelper = new IRBuildHelper(newStmt.getContainer());
        if(rvalue instanceof  NewArray newArrayStmt){
            // 获得base的arrayindex
            ArrayIndex arrayIndex = csManager.getArrayIndex(csObj);
            // 获取长度
            int length = 1;
            if(newArrayStmt.getLength().isConst())
                length = Integer.parseInt(newArrayStmt.getLength().getConstValue().toString());
            ArrayType type = newArrayStmt.getType();
//            Type elementType = (ArrayType)type.elementType();
            CSObj[] elementofArray = new CSObj[length];
            AtomicBoolean f = new AtomicBoolean(false);
            getPointsToSetOf(arrayIndex).forEach(array -> {
                if(array.getObject() instanceof  MockObj mockObj && mockObj.getDescriptor().toString().equals("TaintObj")){
                    f.set(true);
                }
            });
            Type elementType = type.elementType();
            for(int i=-0;i<length;i++){
                var tmpVar = irBuildHelper.newTempVar(type);
                Obj elemObj = heapModel.getMockObj(ARRAY_DESC,tmpVar,elementType,newStmt.getContainer());
                Context elemContext = contextSelector.selectHeapContext(csMethod,elemObj);
                CSObj cselemObj = csManager.getCSObj(elemContext,elemObj);
                elementofArray[i] = cselemObj;
                if(f.get()){
                    propagateNew(csManager.getCSVar(elemContext,tmpVar),getPointsToSetOf(arrayIndex));
                }
            }
            elementsArray.put(arrayIndex,elementofArray);
        }
        else if (rvalue instanceof NewMultiArray) {
            // 获得base的arrayindex
            ArrayIndex arrayIndex = csManager.getArrayIndex(csObj);
            processNewMultiArrayNew(newStmt, arrayIndex, csMethod,irBuildHelper);
        } else{
            if (hasOverriddenFinalize(rvalue)) {
                return processFinalizeRegistration(container, context, newStmt, stmtIterator, stack, csMethod, rvalue, obj,flagInit);
            }
        }

        return false;
    }

    private boolean processFinalizeRegistration(JMethod container, Context context, New newStmt, ChainedIterator<Stmt> stmtIterator, Deque<VisitorState> stack, CSMethod csMethod, NewExp rvalue, Obj obj, AtomicBoolean flagInit){
        Invoke registerInvoke = registerInvokes.computeIfAbsent(newStmt, s -> {
            InvokeStatic callSite = new InvokeStatic(registerRef, Collections.singletonList(s.getLValue()));
            Invoke invoke = new Invoke(csMethod.getMethod(), callSite);
            invoke.setLineNumber(s.getLineNumber());
            return invoke;
        });
        JMethod callee = CallGraphs.resolveCallee(null, registerInvoke);
        if (callee != null) {
            CSCallSite csCallSite = csManager.getCSCallSite(context, registerInvoke);
            Context calleeCtx = contextSelector.selectContext(csCallSite, callee);
            CSMethod csCallee = csManager.getCSMethod(calleeCtx, callee);
            callGraph.addReachableMethod(csCallee);
            reachableMethods.add(callee);
            Edge<CSCallSite, CSMethod> edge = new Edge<>(CallKind.STATIC, csCallSite, csCallee);
            processEdgeTransfer(edge);
            if (edge.getKind() != CallKind.OTHER && !isIgnored(callee)) {
                if (plugin.judgeCheck(edge, null,flagInit)) {
                    stack.push(new VisitorState(container, context, stmtIterator,flagInit));
                    stack.push(new VisitorState(callee, calleeCtx, new ChainedIterator<>(callee.getIR().iterator()),new AtomicBoolean(flagInit.get())));
                    return true;
                }
            }
        }
        return false;
    }

    private void processLoadFieldStatement(Context context, LoadField loadFieldStmt, CSMethod csMethod) {
        Var toVar = loadFieldStmt.getLValue();
        CSVar to = csManager.getCSVar(context, toVar);
        // strong_update
        removeEdges(to);
        JField field = loadFieldStmt.getFieldRef().resolve();
        if (loadFieldStmt.isStatic() && propTypes.isAllowed(loadFieldStmt.getRValue())) {
            StaticField sfield = csManager.getStaticField(field);
            addPFGEdgeAndPropagate(sfield, to, FlowKind.STATIC_LOAD);
        } else if (propTypes.isAllowed(toVar)) {
            FieldAccess fieldAccess = loadFieldStmt.getFieldAccess();
            Var instanceVar = ((InstanceFieldAccess) fieldAccess).getBase();
            CSVar csFromInstanceVar = csManager.getCSVar(context, instanceVar);
            PointsToSet pts = getPointsToSetOf(csFromInstanceVar);
            PointsToSet pts1 = pts.copy();
            pts1.forEach(baseObj -> {
                InstanceField instField = csManager.getInstanceField(baseObj, field);
                addPFGEdgeAndPropagate(instField, to, FlowKind.INSTANCE_LOAD);
            });
        }
        if(getPointsToSetOf(to).isEmpty()){
            IRBuildHelper irBuildHelper = new IRBuildHelper(csMethod.getMethod());
            Type type = field.getType();
            Obj mockObj = heapModel.getMockObj(LHS_DESC,irBuildHelper.newTempVar(type),type,csMethod.getMethod());
            Context context1 = contextSelector.selectHeapContext(csMethod,mockObj);
            propagateNew(to,csManager.getCSObj(context1,mockObj));
        }
    }

    private void processStoreFieldStatement(Context context, StoreField storeFieldStmt, CSMethod csMethod) {
        Var fromVar = storeFieldStmt.getRValue();
        CSVar from = csManager.getCSVar(context, fromVar);
        JField field = storeFieldStmt.getFieldRef().resolve();
        if (propTypes.isAllowed(fromVar)) {
            if (storeFieldStmt.isStatic()) {
                StaticField sfield = csManager.getStaticField(field);
                // strong_update
                removeEdges(sfield);
                addPFGEdgeAndPropagate(from, sfield, FlowKind.STATIC_STORE);
            } else {
                FieldAccess fieldAccess = storeFieldStmt.getFieldAccess();
                Var instanceVar = ((InstanceFieldAccess) fieldAccess).getBase();
                CSVar csToInstanceVar = csManager.getCSVar(context, instanceVar);
                // pts为x.f中x的指向集,可能为o1,o2,o3.为每一个对象构建对应的InstanceField: o1.f ...
                PointsToSet originalSet = getPointsToSetOf(csToInstanceVar);
                PointsToSet pts = originalSet.copy();
                pts.forEach(baseObj -> {
                    if (baseObj.getObject().isFunctional()){
                        InstanceField instField = csManager.getInstanceField(baseObj, field);
                        // strong_update
                        removeEdges(instField);
                        addPFGEdgeAndPropagate(from, instField, FlowKind.INSTANCE_STORE);
                    }
                });
            }

        }
    }

    private void processAssignLiteralStatement(Context context, AssignLiteral assignLiteralStmt, CSMethod csMethod) {
        Literal literal = assignLiteralStmt.getRValue();
        Type type = literal.getType();
        if (type instanceof ClassType) {
            Obj obj = heapModel.getConstantObj((ReferenceLiteral) literal);
            Context heapContext = contextSelector.selectHeapContext(csMethod, obj);
            Var var = assignLiteralStmt.getLValue();
            CSObj csObj = csManager.getCSObj(heapContext, obj);
            addPtsAndPropagate(context, var, csObj);
        }
    }

    private void processCopyStatement(Context context, Copy copyStmt) {
        Var rvalue = copyStmt.getRValue();
        if (propTypes.isAllowed(rvalue)) {
            CSVar from = csManager.getCSVar(context, rvalue);
            CSVar to = csManager.getCSVar(context, copyStmt.getLValue());
            // strong_update
            removeEdges(to);
            addPFGEdgeAndPropagate(from, to, FlowKind.LOCAL_ASSIGN);
        }
    }

    private void processCastStatement(Context context, Cast castStmt) {
        CastExp cast = castStmt.getRValue();
        if (propTypes.isAllowed(cast.getValue())) {
            CSVar from = csManager.getCSVar(context, cast.getValue());
            CSVar to = csManager.getCSVar(context, castStmt.getLValue());
            addPFGEdgeAndPropagate(new PointerFlowEdge(FlowKind.CAST, from, to), cast.getType());

        }
    }

    private void processStoreArrayStatement(Context context, StoreArray storeArrayStmt, CSMethod csMethod) {

        Var rvalue = storeArrayStmt.getRValue();
        CSVar from = csManager.getCSVar(context, rvalue);
        Var toArrayVar = storeArrayStmt.getLValue().getBase();
        CSVar toCSArrayVar = csManager.getCSVar(context, toArrayVar);
        ArrayAccess arrayAccess = storeArrayStmt.getLValue();
        int index = 0;
        if(arrayAccess.getIndex().isConst()) {
            index = Integer.parseInt(arrayAccess.getIndex().getConstValue().toString());
            if (propTypes.isAllowed(rvalue)) {
                PointsToSet ptsArray = getPointsToSetOf(toCSArrayVar);
                for (CSObj csObj : ptsArray) {
                    // arrayIndex表示 r
                    ArrayIndex arrayIndex = csManager.getArrayIndex(csObj);
                    if (elementsArray.containsKey(arrayIndex)) {
                        Pointer elemtIndex;
                        if (elementsArray.get(arrayIndex).length == 0|| index>=elementsArray.get(arrayIndex).length) {
                            elemtIndex = arrayIndex;
                        } else {
                            CSObj csElementObj = elementsArray.get(arrayIndex)[index];
                            // elemtArrayIndex r[0]
                            if(csElementObj.getObject().getType() instanceof  ArrayType) {
                                elemtIndex = csManager.getArrayIndex(csElementObj);
                            }
                            else {
                                Var var = (Var) csElementObj.getObject().getAllocation();
                                elemtIndex = csManager.getCSVar(csElementObj.getContext(),var);
                            }
                        }
                        // strong_update
                        removeEdges(elemtIndex);
                        addPFGEdgeAndPropagate(new PointerFlowEdge(FlowKind.ARRAY_STORE, from, elemtIndex), elemtIndex.getType());

                    }

                }
            }
        }
        else{
            if (propTypes.isAllowed(rvalue)) {
                PointsToSet ptsArray = getPointsToSetOf(toCSArrayVar);
                for (CSObj csObj : ptsArray) {
                    // arrayIndex表示 r
                    Pointer elemtIndex;
                    if(csObj.getObject().getType() instanceof  ArrayType) {
                        elemtIndex = csManager.getArrayIndex(csObj);
                        removeEdges(elemtIndex);
                        addPFGEdgeAndPropagate(new PointerFlowEdge(FlowKind.ARRAY_STORE, from, elemtIndex), elemtIndex.getType());

                    }
                    else {
                        if(csObj.getObject().getAllocation() instanceof  Var var0){
                            elemtIndex = csManager.getCSVar(csObj.getContext(), var0);
                            removeEdges(elemtIndex);
                            addPFGEdgeAndPropagate(new PointerFlowEdge(FlowKind.ARRAY_STORE, from, elemtIndex), elemtIndex.getType());


                        }
                        if (csObj.getObject().getAllocation() instanceof CallSourcePoint csp) {
                            IndexRef indexRef = csp.indexRef();
                            Var var2 = InvokeUtils.getVar(csp.sourceCall(), indexRef.index());
                            elemtIndex = csManager.getCSVar(csObj.getContext(), var2);
                            removeEdges(elemtIndex);
                            addPFGEdgeAndPropagate(new PointerFlowEdge(FlowKind.ARRAY_STORE, from, elemtIndex), elemtIndex.getType());

                        }
                    }
                }
            }
        }



    }

    private void processLoadArrayStatement(Context context, LoadArray loadArrayStmt, CSMethod csMethod) {
        Var lvalue = loadArrayStmt.getLValue();
        CSVar to = csManager.getCSVar(context, lvalue);
        // strong_update
        removeEdges(to);
        ArrayAccess arrayAccess =loadArrayStmt.getArrayAccess();
        Var fromArrayVar = arrayAccess.getBase();
        CSVar from = csManager.getCSVar(context, fromArrayVar);
        int index;
        if(arrayAccess.getIndex().isConst())
            index= Integer.parseInt(arrayAccess.getIndex().getConstValue().toString());
        else {
            index = 0;
        }
        // 首选寻找右值r[index]中r所指向的对象
        PointsToSet ptsArray = getPointsToSetOf(from);
        if (propTypes.isAllowed(lvalue)) {
            ptsArray.forEach(array -> {
                if (array.getObject().isFunctional()) {
                    // 通过对象获取r的arrayindex
                    ArrayIndex arrayIndex = csManager.getArrayIndex(array);
                    // 接着通过elementsArray获取对应元素的对象----r[index]
                    // elemtIndex可能是数组,可能不是数组
                    Pointer elemtIndex;
                    if (elementsArray.containsKey(arrayIndex)) {
                        if(elementsArray.get(arrayIndex).length==0|| index>=elementsArray.get(arrayIndex).length) {
                            elemtIndex = arrayIndex;
                        }
                        else {
                            CSObj csElementObj = elementsArray.get(arrayIndex)[index];
                            // 获取r[index]对应elemtIndex
                            if(csElementObj.getObject().getType() instanceof ArrayType) {
                                elemtIndex = csManager.getArrayIndex(csElementObj);
                            }
                            else{
                                Var var = (Var) csElementObj.getObject().getAllocation();
                                elemtIndex = csManager.getCSVar(csElementObj.getContext(),var);
                            }
                        }

                    }
                    else {
                        elemtIndex = arrayIndex;
                    }
                    // 构建PFG边,r[index]---->左值
                    addPFGEdgeAndPropagate(elemtIndex, to, FlowKind.ARRAY_LOAD);
                }
            });
        }

    }



    // config: 污点默认为全数组传播,取第一个元素
    @Override
    public PointsToSet getPtsArrayElems(Pointer pointer){
        PointsToSet ptsArray = getPointsToSetOf(pointer);
        PointsToSet res = makePointsToSet();
        ptsArray.forEach(array -> {
            if (array.getObject().isFunctional()) {
                // 通过对象获取r的arrayindex
                ArrayIndex arrayIndex = csManager.getArrayIndex(array);
                // 接着通过elementsArray获取对应元素的对象----r[index]
                if (elementsArray.containsKey(arrayIndex)) {
                    // 情况1: 被污染的数组已经初始化,在elementsArray存在对应的元素index
                    // 将所有元素的index的csobj均作为该数组的对象
                    int len = elementsArray.get(arrayIndex).length;
                    if (len == 0) {
                        res.addObject(array);
                    } else {
                        for (int index = 0; index < len; index++) {
                            CSObj csElementObj = elementsArray.get(arrayIndex)[index];
                            res.addObject(csElementObj);
                        }
                    }

                }
                else {
                    // 情况2: 数组为初始化和len=0,情况一样
                    res.addObject(array);
                }
            }
        });

        return  res;
    }

    @Override
    public boolean isContainedArray(Pointer pointer){
        return elementsArray.containsKey(pointer);
    }



    private boolean processInvokeStatement(JMethod container, Context context, Invoke invokeStmt, ChainedIterator<Stmt> stmtIterator, Deque<VisitorState> stack,AtomicBoolean flagInit) {
        if (invokeStmt.isStatic()) {
            return processStaticInvoke(container, context, invokeStmt, stmtIterator, stack,flagInit);
        } else {
            return processInstanceInvoke(container, context, invokeStmt, stmtIterator, stack,flagInit);
        }
    }

    private boolean processStaticInvoke(JMethod container, Context context, Invoke invokeStmt, ChainedIterator<Stmt> stmtIterator, Deque<VisitorState> stack,AtomicBoolean flagInit){
        JMethod callee = CallGraphs.resolveCallee(null, invokeStmt);
        if (callee != null) {
            CSCallSite csCallSite = csManager.getCSCallSite(context, invokeStmt);
            Context calleeCtx = contextSelector.selectContext(csCallSite, callee);
            CSMethod csCallee = csManager.getCSMethod(calleeCtx, callee);
            ChainedIterator<Stmt> calleeStmts = new ChainedIterator<>(callee.getIR().iterator());

            reachableMethods.add(callee);
            boolean f3 = false;
            boolean f1 = false;
            Edge<CSCallSite, CSMethod> edge = new Edge<>(CallKind.STATIC, csCallSite, csCallee);
            if(callGraph.addEdge(edge)) {
                callGraph.addReachableMethod(csCallee);
                processEdgeTransfer(edge);
                if (edge.getKind() != CallKind.OTHER && !isIgnored(callee)) {
                    if(plugin.judgeCallSource(edge, flagInit)){
                        while(calleeStmts.hasNext()){
                            Stmt stmt = calleeStmts.next();
                            if(processStatement(callee,calleeCtx,stmt,calleeStmts,stack,flagInit))
                                break;
                        }
                        plugin.TransferCallSource(edge);
                    } else if(plugin.judgeCheck(edge, null, flagInit)){
                        stack.push(new VisitorState(container, context, stmtIterator, flagInit));
                        stack.push(new VisitorState(callee, calleeCtx, calleeStmts, new AtomicBoolean(true)));
                        f3 = true;

                        // clinit是一个静态方法
                        JMethod clinitMethod = callee.getRef().getDeclaringClass().getDeclaredMethod("<clinit>");
//            JMethod initMethod = callee.getRef().getDeclaringClass().getDeclaredMethod("<init>");
                        if(clinitMethod!=null) {
                            Context clinitCtx = calleeCtx;
                            if (reachableMethods.add(clinitMethod)) {
                                CSMethod csClinit = csManager.getCSMethod(clinitCtx, clinitMethod);
                                callGraph.addReachableMethod(csClinit);
                                stack.push(new VisitorState(callee, calleeCtx, stmtIterator, flagInit));
                                stack.push(new VisitorState(clinitMethod, clinitCtx, new ChainedIterator<>(clinitMethod.getIR().iterator()), new AtomicBoolean(true)));
                                f1 = true;
                            }
                        }
                        plugin.onNewCSMethod(csCallee);
                    }
                }
            }
            return f1 || f3;
        }
        return false;
    }

    private boolean processInstanceInvoke(JMethod container, Context context, Invoke invokeStmt, ChainedIterator<Stmt> stmtIterator, Deque<VisitorState> stack,AtomicBoolean flagInit){
        InvokeExp invokeExp = invokeStmt.getInvokeExp();
        boolean f1 = false;
        if(invokeExp instanceof  InvokeInstanceExp invokeInstanceExpStmt){
            Var var = invokeInstanceExpStmt.getBase();
            CSVar csVar = csManager.getCSVar(context, var);
            PointsToSet originalSet = getPointsToSetOf(csVar);
            PointsToSet copySet = originalSet.copy();
            for (CSObj recvObj : copySet) {
                JMethod callee = CallGraphs.resolveCallee(recvObj.getObject().getType(), invokeStmt);
                if(callee==null){
                    Type objType = var.getType();
                    //变量的类型方法
                    callee = CallGraphs.resolveCallee(objType, invokeStmt);
                }
                if (callee != null) {
                    CSCallSite csCallSite = csManager.getCSCallSite(context, invokeStmt);
                    Context calleeContext = contextSelector.selectContext(csCallSite, recvObj, callee);
                    CSMethod csCallee = csManager.getCSMethod(calleeContext, callee);
                    plugin.onNewCSMethod(csCallee);
                    reachableMethods.add(callee);
                    Edge<CSCallSite, CSMethod> edge = new Edge<>(CallGraphs.getCallKind(invokeStmt), csCallSite, csCallee);
                    if(callGraph.addEdge(edge)){
                        callGraph.addReachableMethod(csCallee);
                        AtomicBoolean calleeFlagInit = new AtomicBoolean(true);
                        if (!flagInit.get()) {
                            calleeFlagInit.set(callee.getName().equals("<init>"));
                        }
                        else {
                            calleeFlagInit.set(true);
                        }
                        processEdgeTransfer(edge);
                        if (edge.getKind() != CallKind.OTHER && !isIgnored(callee)) {
                            if(plugin.judgeCallSource(edge, calleeFlagInit)){
                                addPtsAndPropagate(calleeContext, callee.getIR().getThis(), recvObj);
                                ChainedIterator<Stmt> stmtChainedIterator = new ChainedIterator<>(callee.getIR().iterator());
                                Deque<VisitorState> subStack = new ArrayDeque<>();
                                subStack.push(new VisitorState(callee,calleeContext,stmtChainedIterator,calleeFlagInit));
                                while(!subStack.isEmpty()) {
                                    VisitorState state = subStack.pop();
                                    ChainedIterator<Stmt> stmtChainedIterator1 = state.stmts;
                                    while (stmtChainedIterator1.hasNext()) {
                                        Stmt stmt = stmtChainedIterator1.next();
                                        if (processStatement(state.container, state.context, stmt, stmtChainedIterator1, subStack, state.flaginit))
                                            break;
                                    }
                                }
                                plugin.TransferCallSource(edge);
                            }
                            else if (plugin.judgeCheck(edge, csVar, calleeFlagInit)) {
                                addPtsAndPropagate(calleeContext, callee.getIR().getThis(), recvObj);
                                stack.push(new VisitorState(container, context, stmtIterator, flagInit));
                                stack.push(new VisitorState(callee, calleeContext, new ChainedIterator<>(callee.getIR().iterator()), calleeFlagInit));
                                f1 = true;

                            }


                        }
                        if(!invokeStmt.isDynamic()){
                            plugin.reflectionHandler(csCallee,invokeStmt);
                        }
                        plugin.onNewCallEdge(edge);
                    }
                } else
                    plugin.onUnresolvedCall(recvObj, context, invokeStmt);
            }

        }
        else
            f1 = false;

        return f1;
    }

    // 定义基本类型和不可变类型集合
    private static final Set<Class<?>> IMMUTABLE_TYPES = new HashSet<>();
    static {
        IMMUTABLE_TYPES.add(String.class);
        IMMUTABLE_TYPES.add(Boolean.class);
        IMMUTABLE_TYPES.add(Byte.class);
        IMMUTABLE_TYPES.add(Short.class);
        IMMUTABLE_TYPES.add(Integer.class);
        IMMUTABLE_TYPES.add(Long.class);
        IMMUTABLE_TYPES.add(Float.class);
        IMMUTABLE_TYPES.add(Double.class);
        IMMUTABLE_TYPES.add(Character.class);
    }



    public void processEdgeTransfer(Edge<CSCallSite, CSMethod> edge){

        CSMethod csCallee = edge.getCallee();
        // 调用点所在的上下文
        Context callerCtx = edge.getCallSite().getContext();
        Invoke callSite = edge.getCallSite().getCallSite();
        //调用点所产生的上下文
        Context calleeCtx = csCallee.getContext();
        JMethod callee = csCallee.getMethod();
        InvokeExp invokeExp = callSite.getInvokeExp();
        if(callee.isAbstract())
            return;
        // pass arguments to parameters
        // 参数传递arg-param
        for (int i = 0; i < invokeExp.getArgCount(); ++i) {
            Var arg = invokeExp.getArg(i);
            if (propTypes.isAllowed(arg)) {
                Var param = callee.getIR().getParam(i);
                CSVar argVar = csManager.getCSVar(callerCtx, arg);
                CSVar paramVar = csManager.getCSVar(calleeCtx, param);
                addPFGEdgeAndPropagate(argVar, paramVar, FlowKind.PARAMETER_PASSING);
            }
        }
        // 处理除基本类型（如 int、float、boolean 等）,不可变类型（如 String 和所有 Wrapper 类）外引用类型（如对象、数组等）的双向传递
        for (int i = 0; i < invokeExp.getArgCount(); ++i) {
            Var arg = invokeExp.getArg(i);
            try {
                if (propTypes.isAllowed(arg) && !(isImmutable(Class.forName(arg.getType().getName()))) && !isWrapperType(Class.forName(arg.getType().getName()))) {
                    Var param = callee.getIR().getParam(i);
                    CSVar argVar = csManager.getCSVar(callerCtx, arg);
                    CSVar paramVar = csManager.getCSVar(calleeCtx, param);
                    // 创建PFG的边
                    PointerFlowEdge edgeParamToArg = new PointerFlowEdge(FlowKind.PARAMETER_PASSING, paramVar, argVar);
                    edgeParamToArg = pointerFlowGraph.addEdge(edgeParamToArg);
                    if (edgeParamToArg != null)
                        edgeParamToArg.addTransfer(Identity.get());
                }
            } catch (ClassNotFoundException e) {

            } catch (NoClassDefFoundError e) {

            }
        }

        // pass results to LHS variable
        Var lhs = callSite.getResult();
        if (lhs != null && propTypes.isAllowed(lhs)) {
            CSVar csLHS = csManager.getCSVar(callerCtx, lhs);
            for (Var ret : callee.getIR().getReturnVars()) {
                if (propTypes.isAllowed(ret)) {
                    CSVar csRet = csManager.getCSVar(calleeCtx, ret);
                    addPFGEdgeAndPropagate(csRet, csLHS, FlowKind.RETURN);
                }
            }
        }
    }
    // 判断类型是否为不可变类型
    public static boolean isImmutable(Class<?> clazz) {
        return IMMUTABLE_TYPES.contains(clazz) || clazz.isPrimitive();
    }

    // 判断类型是否为包装类
    private static boolean isWrapperType(Class<?> clazz) {
        return  IMMUTABLE_TYPES.contains(clazz);
    }

    public void addPtsAndPropagate(Context context,Var var,Context heapContext,Obj obj){
          addPtsAndPropagate(context,var,csManager.getCSObj(heapContext,obj));
    }
    public void addPtsAndPropagate(Context context,Var var,CSObj csObj){
        Pointer pointer = csManager.getCSVar(context,var);
        addPtsAndPropagate(pointer,csObj);
    }
    public void addPtsAndPropagate(Pointer pointer,Context heapContext,Obj obj){
        CSObj csObj = csManager.getCSObj(heapContext,obj);
        addPtsAndPropagate(pointer,csObj);
    }
    public void addPtsAndPropagate(Pointer pointer,CSObj csObj){
        PointsToSet pts = makePointsToSet();
        pts.addObject(csObj);
        propagateNew(pointer,pts);
    }


    public void addPFGEdgeAndPropagate(Pointer source, Pointer target, FlowKind kind){
        // 创建PFG的边
        PointerFlowEdge edge = new PointerFlowEdge(kind,source,target);
        Transfer transfer = Identity.get();
        edge = pointerFlowGraph.addEdge(edge);
        if (edge != null && edge.addTransfer(transfer)) {
            PointsToSet targetSet = transfer.apply(
                    edge, getPointsToSetOf(edge.source()));
            if (!targetSet.isEmpty()) {
                //传播
                propagateNew(edge.target(), targetSet);
            }
        }
    }

    @Override
    public void addPFGEdgeAndPropagate(PointerFlowEdge edge, Transfer transfer){
        // 创建PFG的边
        edge = pointerFlowGraph.addEdge(edge);
        if (edge != null && edge.addTransfer(transfer)) {
            PointsToSet targetSet = transfer.apply(
                    edge, getPointsToSetOf(edge.source()));
            getPointsToSetOf(edge.source()).forEach(csobj ->{
                if(csobj.getObject() instanceof MockObj mockObj && mockObj.getDescriptor().string().equals("TaintObj"))
                    targetSet.addObject(csobj);
            });
            if (!targetSet.isEmpty()) {
                //传播
                propagateNew(edge.target(), targetSet);
            }
        }
    }




    @Override
    public void addEntryPoint(EntryPoint entryPoint) {
        Context entryCtx = contextSelector.getEmptyContext();
        JMethod entryMethod = entryPoint.method();
        CSMethod csEntryMethod = csManager.getCSMethod(entryCtx, entryMethod);
        callGraph.addEntryMethod(csEntryMethod);

        Deque<VisitorState> stack = new ArrayDeque<>();
        stack.push(new VisitorState(entryMethod, entryCtx, new ChainedIterator<>(entryMethod.getIR().iterator()), new AtomicBoolean(true)));

        IR ir = entryMethod.getIR();
        ParamProvider paramProvider = entryPoint.paramProvider();

        if (!entryMethod.isStatic()) {
            propagateObjects(ir.getThis(), entryCtx, paramProvider.getThisObjs());
        }

        for (int i = 0; i < entryMethod.getParamCount(); ++i) {
            propagateObjects(ir.getParam(i), entryCtx, paramProvider.getParamObjs(i));
        }

        paramProvider.getFieldObjs().forEach((base, field, obj) -> {
            CSObj csBase = csManager.getCSObj(entryCtx, base);
            InstanceField iField = csManager.getInstanceField(csBase, field);
            addPtsAndPropagate(iField, entryCtx, obj);
        });

        paramProvider.getArrayObjs().forEach((array, elem) -> {
            CSObj csArray = csManager.getCSObj(entryCtx, array);
            ArrayIndex arrayIndex = csManager.getArrayIndex(csArray);
            addPtsAndPropagate(arrayIndex, entryCtx, elem);
        });

        processMethodStack(stack);
    }

    private void propagateObjects(Var variable, Context context, Collection<Obj> objects) {
        for (Obj obj : objects) {
            addPtsAndPropagate(context, variable, context, obj);
        }
    }

    private void processMethodStack(Deque<VisitorState> stack) {
        while (!stack.isEmpty()) {
            VisitorState state = stack.pop();
            ChainedIterator<Stmt> stmtIterator = state.stmts;
            while (stmtIterator.hasNext()) {
                Stmt stmt = stmtIterator.next();
                if (processStatement(state.container, state.context, stmt, stmtIterator, stack, state.flaginit)) {
                    break;
                }
            }
        }
    }

    private void  processNewMultiArrayNew(New allocSite, ArrayIndex arrayIndexBase,CSMethod csMethod,IRBuildHelper irBuildHelper){
        NewMultiArray newMultiArray = (NewMultiArray) allocSite.getRValue();
        // 获得第一维的长度
        int len = 1;
        int len2 = 1;
        if(newMultiArray.getLength(0).isConst())
            len = Integer.parseInt(newMultiArray.getLength(0).getConstValue().toString());
        if(newMultiArray.getLength(1).isConst())
            len2 = Integer.parseInt(newMultiArray.getLength(1).getConstValue().toString());
        ArrayType type = newMultiArray.getType();
        CSObj[] elementOfArray1 = new CSObj[len];
        for(int i=0;i<len;i++){
            Var tmpVar = irBuildHelper.newTempVar(type);
            Obj elemArrayObj = heapModel.getMockObj(MULTI_ARRAY_DESC,tmpVar,type,allocSite.getContainer());
            Context elemArrayContext = contextSelector.selectHeapContext(csMethod,elemArrayObj);
            CSObj cselemArrayObj = csManager.getCSObj(elemArrayContext,elemArrayObj);
            elementOfArray1[i] = cselemArrayObj;
            // second
            ArrayIndex arrayIndex = csManager.getArrayIndex(cselemArrayObj);
            // 传播
            propagateNew(arrayIndex,cselemArrayObj);
            CSObj[] elementOfArray2 = new CSObj[len2];
            Type elementType = type.elementType();
            for(int j=0;j<len2;j++){
                Var tmpVar1 = irBuildHelper.newTempVar(elementType);
                Obj elemArrayObj2 = heapModel.getMockObj(MULTI_ARRAY_DESC,tmpVar1,elementType,allocSite.getContainer());
                Context elemArrayContext2 = contextSelector.selectHeapContext(csMethod,elemArrayObj2);
                CSObj cselemArrayObj2 = csManager.getCSObj(elemArrayContext2,elemArrayObj2);
                elementOfArray2[j] = cselemArrayObj2;
            }
            elementsArray.put(arrayIndex,elementOfArray2);
        }
        elementsArray.put(arrayIndexBase,elementOfArray1);

    }


    private boolean hasOverriddenFinalize(NewExp newExp) {
        return !finalize.equals(
                hierarchy.dispatch(newExp.getType(), finalizeRef));
    }



    @Override
    public void addCallEdge(Edge<CSCallSite, CSMethod> edge) {
        workList.addEntry(edge);
    }


    //处理新的上下文被调用的方法
    @Override
    public void addCSMethod(CSMethod csMethod) {
        if (callGraph.addReachableMethod(csMethod)) {
            // process new reachable context-sensitive method
            JMethod method = csMethod.getMethod();
            if (isIgnored(method)) {
                return;
            }
            processNewMethod(method);
            // 处理方法语句
            addStmts(csMethod, method.getIR().getStmts());
            plugin.onNewCSMethod(csMethod);
        }
    }

    @Override
    public void addStmts(CSMethod csMethod, Collection<Stmt> stmts) {

    }


    @Override
    public void addIgnoredMethod(JMethod method) {
        ignoredMethods.add(method);
    }

    @Override
    public void initializeClass(JClass cls) {
        if (cls == null || initializedClasses.contains(cls)) {
            return;
        }
        // initialize super class
        JClass superclass = cls.getSuperClass();
        if (superclass != null) {
            initializeClass(superclass);
        }
        // TODO: initialize the superinterfaces which
        //  declare default methods
        JMethod clinit = cls.getClinit();
        Deque<VisitorState> stack = new ArrayDeque<>();
        if (clinit != null) {
            // addCSMethod() may trigger initialization of more
            // classes. So cls must be added before addCSMethod(),
            // otherwise, infinite recursion may occur.
            initializedClasses.add(cls);
            CSMethod csMethod = csManager.getCSMethod(
                    contextSelector.getEmptyContext(), clinit);
//            addCSMethod(csMethod);
            if (callGraph.addReachableMethod(csMethod)) {
                // process new reachable context-sensitive method
                JMethod method = csMethod.getMethod();
                if (isIgnored(method)) {
                    return;
                }
                ChainedIterator<Stmt> stmtChainedIterator = new ChainedIterator<>(method.getIR().iterator());
                while(stmtChainedIterator.hasNext()){
                    Stmt stmt = stmtChainedIterator.next();
                    if(processStatement(method,csMethod.getContext(),stmt,stmtChainedIterator,stack,new AtomicBoolean(true)))
                        break;
                }
//                plugin.onNewCSMethod(csMethod);
            }

        }
    }

    @Override
    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(
                    propTypes, csManager, heapModel,
                    callGraph, pointerFlowGraph);
        }
        return result;
    }
}
