package pascal.taie.analysis.pta.plugin.taint;

import pascal.taie.World;
import pascal.taie.analysis.pta.core.solver.DeclaredParamProvider;
import pascal.taie.analysis.pta.core.solver.EmptyParamProvider;
import pascal.taie.analysis.pta.core.solver.EntryPoint;
import pascal.taie.analysis.pta.core.solver.Solver;
import pascal.taie.analysis.pta.plugin.Plugin;
import pascal.taie.language.classes.JMethod;

/**
 * Initializes standard entry points for pointer analysis.
 */
public class SpringBootEntryPointHandler implements Plugin {

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
    }
}
