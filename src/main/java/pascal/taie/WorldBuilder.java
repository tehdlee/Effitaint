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

package pascal.taie;

import pascal.taie.config.AnalysisConfig;
import pascal.taie.config.Options;

import java.util.List;

/**
 * Interface for {@link World} builder.
 */
public interface WorldBuilder {

    /**
     * Builds a new instance of {@link World} and make it globally accessible
     * through static methods of {@link World}.
     * TODO: remove {@code analyses}.
     *
     * @param options  the options
     * @param analyses the analyses to be executed
     */
    void build(Options options, List<AnalysisConfig> analyses);
}
