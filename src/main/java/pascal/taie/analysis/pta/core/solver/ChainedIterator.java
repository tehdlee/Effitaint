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

import java.util.*;

public class ChainedIterator<T> implements Iterator<T> {
    private final Deque<Iterator<T>> iterators = new ArrayDeque<>();

    public ChainedIterator(Iterator<T>... iterators) {
        this.iterators.addAll(Arrays.asList(iterators));
    }

    @Override
    public boolean hasNext() {
        while (!iterators.isEmpty()) {
            if (iterators.peek().hasNext()) {
                return true;
            } else {
                iterators.pop();
            }
        }
        return false;
    }

    @Override
    public T next() {
        if (hasNext()) {
            return iterators.peek().next();
        }
        throw new NoSuchElementException();
    }

    public void addIterator(Iterator<T> iterator) {
        iterators.push(iterator);
    }
}

