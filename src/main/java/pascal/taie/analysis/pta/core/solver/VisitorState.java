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

import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;

import java.util.concurrent.atomic.AtomicBoolean;

// VisitorState class to maintain state
public class VisitorState {
    JMethod container;
    Context context;
    ChainedIterator<Stmt> stmts;
    AtomicBoolean flaginit;

    VisitorState(JMethod container, Context context, ChainedIterator<Stmt> stmts,AtomicBoolean flaginit) {
        this.container = container;
        this.context = context;
        this.stmts = stmts;
        this.flaginit = flaginit;
    }
}
