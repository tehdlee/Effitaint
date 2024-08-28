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

import pascal.taie.language.classes.JMethod;

import javax.annotation.Nonnull;
import java.util.Comparator;

/**
 * A {@code ParamSourcePoint} is a parameter of a method.
 */
public record ParamSourcePoint(JMethod sourceMethod, IndexRef indexRef)
        implements SourcePoint {

    private static final Comparator<ParamSourcePoint> COMPARATOR =
            Comparator.comparing((ParamSourcePoint psp) -> psp.sourceMethod.toString())
                    .thenComparing(ParamSourcePoint::indexRef);

    @Override
    public int compareTo(@Nonnull SourcePoint sp) {
        if (sp instanceof ParamSourcePoint psp) {
            return COMPARATOR.compare(this, psp);
        }
        return SourcePoint.compare(this, sp);
    }

    @Override
    public JMethod getContainer() {
        return sourceMethod;
    }

    @Override
    public int getPriority() {
        return 0;
    }

    @Override
    public String toString() {
        return sourceMethod + "/" + indexRef;
    }
}
