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

package pascal.taie;

import org.apache.logging.log4j.Level;
import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.analysis.AnalysisManager;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.config.AnalysisPlanner;
import pascal.taie.config.ConfigManager;
import pascal.taie.config.Configs;
import pascal.taie.config.LoggerConfigs;
import pascal.taie.config.Options;
import pascal.taie.config.Plan;
import pascal.taie.config.PlanConfig;
import pascal.taie.config.Scope;
import pascal.taie.frontend.cache.CachedWorldBuilder;
import pascal.taie.util.Timer;
import pascal.taie.util.collection.Lists;

import java.io.InputStream;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.util.List;
//import java.util.Timer;
import java.util.TimerTask;

public class Main {

    private static final Logger logger = LogManager.getLogger(Main.class);
//    private static long maxMemoryUsed = 0;
    public static void main(String... args) {
//        Timer timer = new Timer(true);
//        timer.scheduleAtFixedRate(new TimerTask() {
//            @Override
//            public void run() {
//                Runtime runtime = Runtime.getRuntime();
//                long usedMemory = runtime.totalMemory() - runtime.freeMemory();
//                if (usedMemory > maxMemoryUsed) {
//                    maxMemoryUsed = usedMemory;
//                }
//            }
//        }, 0, 1000);
        Timer.runAndCount(() -> {
            Options options = processArgs(args);
            LoggerConfigs.setOutput(options.getOutputDir());
            Plan plan = processConfigs(options);
            if (plan.analyses().isEmpty()) {
                logger.info("No analyses are specified");
                System.exit(0);
            }
            buildWorld(options, plan.analyses());
            executePlan(plan);
            LoggerConfigs.reconfigure();
        }, "Tai-e");

        // 打印最大内存使用量
//        Runtime.getRuntime().addShutdownHook(new Thread(() -> {
//            double maxMemoryUsedGB = maxMemoryUsed / (1024.0 * 1024 * 1024);
//            logger.info(String.format("Max memory used: %.2f GB", maxMemoryUsedGB));
//        }));
    }


    /**
     * If the given options is empty or specify to print help information,
     * then print help and exit immediately.
     */
    private static Options processArgs(String... args) {
        Options options = Options.parse(args);
        if (options.isPrintHelp() || args.length == 0) {
            options.printHelp();
            System.exit(0);
        }
        return options;
    }

    private static Plan processConfigs(Options options) {
        InputStream content = Configs.getAnalysisConfig();
        List<AnalysisConfig> analysisConfigs = AnalysisConfig.parseConfigs(content);
        ConfigManager manager = new ConfigManager(analysisConfigs);
        AnalysisPlanner planner = new AnalysisPlanner(
                manager, options.getKeepResult());
        boolean reachableScope = options.getScope().equals(Scope.REACHABLE);
        if (!options.getAnalyses().isEmpty()) {
            // Analyses are specified by options
            List<PlanConfig> planConfigs = PlanConfig.readConfigs(options);
            manager.overwriteOptions(planConfigs);
            Plan plan = planner.expandPlan(
                    planConfigs, reachableScope);
            // Output analysis plan to file.
            // For outputting purpose, we first convert AnalysisConfigs
            // in the expanded plan to PlanConfigs
            planConfigs = Lists.map(plan.analyses(),
                    ac -> new PlanConfig(ac.getId(), ac.getOptions()));
            // TODO: turn off output in testing?
            PlanConfig.writeConfigs(planConfigs, options.getOutputDir());
            if (!options.isOnlyGenPlan()) {
                // This run not only generates plan file but also executes it
                return plan;
            }
        } else if (options.getPlanFile() != null) {
            // Analyses are specified by file
            List<PlanConfig> planConfigs = PlanConfig.readConfigs(options.getPlanFile());
            manager.overwriteOptions(planConfigs);
            return planner.makePlan(planConfigs, reachableScope);
        }
        // No analyses are specified
        return Plan.emptyPlan();
    }

    /**
     * Convenient method for building the world from String arguments.
     */
    public static void buildWorld(String... args) {
        Options options = Options.parse(args);
        LoggerConfigs.setOutput(options.getOutputDir());
        Plan plan = processConfigs(options);
        buildWorld(options, plan.analyses());
        LoggerConfigs.reconfigure();
    }

    private static void buildWorld(Options options, List<AnalysisConfig> analyses) {
        Timer.runAndCount(() -> {
            try {
                Class<? extends WorldBuilder> builderClass = options.getWorldBuilderClass();
                Constructor<? extends WorldBuilder> builderCtor = builderClass.getConstructor();
                WorldBuilder builder = builderCtor.newInstance();
                if (options.isWorldCacheMode()) {
                    builder = new CachedWorldBuilder(builder);
                }
                builder.build(options, analyses);
                logger.info("{} classes with {} methods in the world",
                        World.get()
                                .getClassHierarchy()
                                .allClasses()
                                .count(),
                        World.get()
                                .getClassHierarchy()
                                .allClasses()
                                .mapToInt(c -> c.getDeclaredMethods().size())
                                .sum());
            } catch (InstantiationException | IllegalAccessException |
                    NoSuchMethodException | InvocationTargetException e) {
                System.err.println("Failed to build world due to " + e);
                System.exit(1);
            }
        }, "WorldBuilder");
    }

    private static void executePlan(Plan plan) {
        new AnalysisManager(plan).execute();
    }
}
