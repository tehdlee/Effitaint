/*
 * EffiTaint: A Static Taint Analysis Tool Based on Tai-e
 *
 * Copyright (C) 2024 [Li Haocheng] <[ishaocheng@163.com]>
 *
 * Modifications in this file are part of the EffiTaint project,
 * which is based on Tai-e. These modifications are licensed under
 * the same terms as Tai-e, the GNU Lesser General Public License v3.0.
 */

package pascal.taie.analysis.pta.plugin.taint;

import pascal.taie.ir.IR;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.*;

public class MethodCollector {
    private final Set<String> sourcesMethodStr;
    private final List<JClass> classList;
    private final Set<JMethod> methodsOfContainSources = new HashSet<>();
    private final Set<String> methodsStrOfSourcesContainer = new HashSet<>();
    private final Map<JField, Type> fieldSources;

    public MethodCollector(Set<String> sourcesMethodStr, List<JClass> classList,Map<JField, Type> fieldSources) {
        this.sourcesMethodStr = sourcesMethodStr;
        this.classList = classList;
        this.fieldSources = fieldSources;
    }

    public Pair<Set<JMethod>,Set<String>> collectMethods() {
        Set<String> currentMethodStr = new HashSet<>(sourcesMethodStr);
        Set<JMethod> processedMethods = new HashSet<>();
        boolean flag = true;

        while (!currentMethodStr.isEmpty()) {
            Set<String> newMethodStr = new HashSet<>();

            for (JClass jClass : classList) {
                Collection<JMethod> methods = jClass.getDeclaredMethods();
                for (JMethod jMethod : methods) {
                    if (jMethod.isAbstract() || jMethod.isNative()) {
                        continue;
                    }

                    IR ir = jMethod.getIR();
                    if (ir == null) {
                        continue;
                    }
                    if (processedMethods.contains(jMethod)) {
                        continue; // Skip already processed methods
                    }

                    boolean invokeFound = ir.invokes(false)
                            .map(invokeStmt -> invokeStmt.getMethodRef().getName())
                            .anyMatch(currentMethodStr::contains);

                    boolean loadFieldFound = false;
                    if (!invokeFound) {
                        loadFieldFound = ir.stmts()
                                .filter(stmt -> stmt instanceof LoadField)
                                .map(stmt -> (LoadField) stmt)
                                .anyMatch(loadFieldStmt -> {
                                    JField field = loadFieldStmt.getFieldRef().resolve();
                                    Type type = fieldSources.get(field);
                                    return type != null;
                                });
                    }

                    if ((invokeFound || loadFieldFound) && conditionS(jMethod)) {
                        newMethodStr.add(jMethod.getName());
                        processedMethods.add(jMethod);
                        if(flag){
                            ir.invokes(false).map(invokeStmt -> invokeStmt.getMethodRef().getName())
                                    .forEach(methodsStrOfSourcesContainer::add);
                            addClassAndAncestorsMethods(jMethod.getDeclaringClass(), processedMethods, methodsStrOfSourcesContainer);
                        }

                    }
                }
            }
            flag = false;

            if (newMethodStr.isEmpty()) {
                break; // Stop if no new methods are found
            }

            currentMethodStr = newMethodStr; // Update for next iteration
        }

        return new Pair<>(methodsOfContainSources,methodsStrOfSourcesContainer);
    }

    private boolean conditionS(JMethod jMethod) {
        return methodsOfContainSources.add(jMethod); // Returns true if jMethod was not already in the set
    }
    private void addClassAndAncestorsMethods(JClass jClass, Set<JMethod> processedMethods, Set<String> methodsStrOfSourcesContainer) {
        while (jClass != null && !jClass.getName().equals("java.lang.Object")) {
            for (JMethod method : jClass.getDeclaredMethods()) {
                if (!processedMethods.contains(method)|| !method.isAbstract()|| !method.isNative()) {
                    processedMethods.add(method);
                    methodsStrOfSourcesContainer.add(method.getName());
                }
            }
            jClass = jClass.getSuperClass();
        }
    }

}


class Pair<T, U> {
    private final T first;
    private final U second;

    public Pair(T first, U second) {
        this.first = first;
        this.second = second;
    }

    public T methodsOfContainSources() {
        return first;
    }

    public U methodsStrOfSourcesContainer() {
        return second;
    }
}
