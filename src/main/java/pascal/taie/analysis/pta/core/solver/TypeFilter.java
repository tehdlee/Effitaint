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

import pascal.taie.analysis.pta.core.heap.MockObj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.language.type.NullType;
import pascal.taie.language.type.ReferenceType;
import pascal.taie.language.type.Type;
import pascal.taie.language.type.TypeSystem;

import java.util.function.Supplier;

/**
 * Transfer function that filters out the objects whose types are NOT
 * subtypes of specific type.
 */
public class TypeFilter implements Transfer {

    /**
     * The guard type.
     */
    private final Type type;

    private final TypeSystem typeSystem;

    private final Supplier<PointsToSet> ptsFactory;

    public TypeFilter(Type type, Solver solver) {
        this.type = type;
        this.typeSystem = solver.getTypeSystem();
        this.ptsFactory = solver::makePointsToSet;
    }

    @Override
    public PointsToSet apply(PointerFlowEdge edge, PointsToSet input) {
        PointsToSet result = ptsFactory.get();
        input.objects().forEach(o -> {
            if (isAssignable(o.getObject().getType(), type)) {
                result.addObject(o);
            }
//            } else if(o.getObject() instanceof MockObj mockObj){
//                // 修改 o 的类型为 type
//                mockObj.setType(type);
//                result.addObject(o);
//            }
        });
        return result;
    }

    private boolean isAssignable(Type from, Type to) {
        return (from instanceof NullType)
                ? to instanceof ReferenceType
                : typeSystem.isSubtype(to, from);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) {
            return true;
        }
        if (!(o instanceof TypeFilter that)) {
            return false;
        }
        return type.equals(that.type);
    }

    @Override
    public int hashCode() {
        return type.hashCode();
    }
}
