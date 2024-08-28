/*
 * EffiTaint: A Static Taint Analysis Tool Based on Tai-e
 *
 * Copyright (C) 2024 [Li Haocheng] <[ishaocheng@163.com]>
 *
 * Modifications in this file are part of the EffiTaint project,
 * which is based on Tai-e. These modifications are licensed under
 * the same terms as Tai-e, the GNU Lesser General Public License v3.0.
 */
// FieldInfo class
package pascal.taie.analysis.pta.plugin.reflection;

import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JClass;

import javax.annotation.Nullable;
import java.util.Set;

public record FieldInfo(Invoke invoke, @Nullable JClass clazz, @Nullable String name) {

    private static final Set<String> GET_FIELD =
            Set.of("getField", "getFields");

    private static final Set<String> GET_DECLARED_FIELD =
            Set.of("getDeclaredField", "getDeclaredFields");

    public boolean isFromGetField() {
        return GET_FIELD.contains(invoke.getMethodRef().getName());
    }

    public boolean isFromGetDeclaredField() {
        return GET_DECLARED_FIELD.contains(invoke.getMethodRef().getName());
    }

    public boolean isClassUnknown() {
        return clazz == null;
    }

    public boolean isNameUnknown() {
        return name == null;
    }
}



