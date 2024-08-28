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

import pascal.taie.World;
import pascal.taie.analysis.pta.core.solver.DeclaredParamProvider;
import pascal.taie.analysis.pta.core.solver.EmptyParamProvider;
import pascal.taie.analysis.pta.core.solver.EntryPoint;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;

import java.util.List;

/**
 * Initializes standard entry points for pointer analysis.
 */
public class EntryPointHandler implements Plugin {

    private Solver solver;

    @Override
    public void setSolver(Solver solver) {
        this.solver = solver;
    }

    @Override
    public void onStart() {
        // process program main method
        JMethod main = World.get().getMainMethod();
        if (main != null) {
            solver.addEntryPoint(new EntryPoint(main,
                    new DeclaredParamProvider(main, solver.getHeapModel(), 1)));
        }
        // process implicit entries
        if (solver.getOptions().getBoolean("implicit-entries")) {
            for (JMethod entry : World.get().getImplicitEntries()) {
                solver.addEntryPoint(new EntryPoint(entry, EmptyParamProvider.get()));
            }
        }
//        List<JClass> list = solver.getHierarchy().applicationClasses().toList();
//        for (JClass jClass : list) {
//            jClass.getDeclaredMethods().forEach(jMethod->{
//                if (!jMethod.getAnnotations().stream().filter(
//                        annotation -> annotation.getType().matches("org.springframework.web.bind.annotation.\\w+Mapping")
//                ).toList().isEmpty()) {
//                    solver.addEntryPoint(new EntryPoint(jMethod, EmptyParamProvider.get()));
//                }
//            });
//
//
//        }
    }
}
