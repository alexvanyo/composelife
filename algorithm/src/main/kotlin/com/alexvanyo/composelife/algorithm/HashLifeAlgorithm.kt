/*
 * Copyright 2022 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.alexvanyo.composelife.algorithm

import androidx.annotation.IntRange
import androidx.compose.ui.unit.IntOffset
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.model.HashLifeCellState
import com.alexvanyo.composelife.model.MacroCell
import com.alexvanyo.composelife.model.expandCentered
import com.alexvanyo.composelife.model.toHashLifeCellState
import com.google.common.base.Equivalence
import com.google.common.base.Ticker
import com.google.common.cache.CacheBuilder
import com.google.common.cache.CacheLoader
import com.google.common.cache.LoadingCache
import kotlinx.coroutines.withContext
import java.util.concurrent.TimeUnit
import javax.inject.Inject

class HashLifeAlgorithm @Inject constructor(
    private val dispatchers: ComposeLifeDispatchers,
) : GameOfLifeAlgorithm {

    /**
     * The current number of computed generations.
     *
     * Note this does not have any direct relation to the current generation count of a specific genealogy, since
     * this same instance can be used to compute multiple genealogies.
     *
     * This value is used to prune the caches of [canonicalCellMap] and [cellMap].
     */
    private var computedGenerations = 0L

    /**
     * An implementation of [Ticker] backed by [computedGenerations].
     *
     * This is a slight misuse of the [Ticker] API, since [computedGenerations] has no relation to nanoseconds.
     * However, we can use this to expire entries after a set number of generations.
     */
    private val computedGenerationTicker = object : Ticker() {
        override fun read(): Long = computedGenerations
    }

    /**
     * The map containing the "canonical" [MacroCell.CellNode]s. This ensures that there is exactly one instance of
     * each equivalent [MacroCell.CellNode] (which makes comparing [MacroCell.CellNode]s possible in O(1) with just
     * reference checking).
     *
     * The keys of this map must already have canonical subnodes, which is ensured by the implementation of
     * [makeCanonical].
     */
    private val canonicalCellMap:
        LoadingCache<Equivalence.Wrapper<MacroCell.CellNode>, MacroCell.CellNode> =
            CacheBuilder.newBuilder()
                .ticker(computedGenerationTicker)
                .expireAfterAccess(256, TimeUnit.NANOSECONDS)
                .build(
                    object : CacheLoader<Equivalence.Wrapper<MacroCell.CellNode>, MacroCell.CellNode>() {
                        override fun load(key: Equivalence.Wrapper<MacroCell.CellNode>): MacroCell.CellNode =
                            key.get().makeCanonical(false)
                    },
                )

    /**
     * The memoization map for [MacroCell.CellNode.computeNextGeneration].
     */
    private val cellMap: LoadingCache<Equivalence.Wrapper<MacroCell.CellNode>, MacroCell.CellNode> =
        CacheBuilder.newBuilder()
            .ticker(computedGenerationTicker)
            .expireAfterAccess(256, TimeUnit.NANOSECONDS)
            .build(
                object : CacheLoader<Equivalence.Wrapper<MacroCell.CellNode>, MacroCell.CellNode>() {
                    override fun load(key: Equivalence.Wrapper<MacroCell.CellNode>): MacroCell.CellNode =
                        key.get().computeNextGeneration(false)
                },
            )

    private fun MacroCell.makeCanonical(useMap: Boolean = true): MacroCell =
        when (this) {
            is MacroCell.Cell -> this
            is MacroCell.CellNode -> makeCanonical(useMap = useMap)
        }

    private fun MacroCell.CellNode.makeCanonical(useMap: Boolean = true): MacroCell.CellNode {
        val currentEntry = canonicalCellMap.asMap()[CanonicalMacroCellEquivalence.wrap(this)]

        return if (currentEntry != null) {
            // Fast path: return the canonical cell if already in the map
            // There should be no reason to be making a cell canonical without the map if it is already in the map
            check(useMap)
            currentEntry
        } else {
            // Slow path: make all subnodes canonical, to check if we have an equivalent canonical node
            val withCanonicalSubNodes = if (size == 0) {
                // Special case: if this is an empty node, then all subnodes will have the same canonical node.
                val smallerEmptyCellNode = nw.makeCanonical()
                MacroCell.CellNode(
                    nw = smallerEmptyCellNode,
                    ne = smallerEmptyCellNode,
                    sw = smallerEmptyCellNode,
                    se = smallerEmptyCellNode,
                )
            } else {
                MacroCell.CellNode(
                    nw = nw.makeCanonical(),
                    ne = ne.makeCanonical(),
                    sw = sw.makeCanonical(),
                    se = se.makeCanonical(),
                )
            }

            if (useMap) {
                // If we're using the map, pull from it now with canonical cell nodes
                canonicalCellMap[CanonicalMacroCellEquivalence.wrap(withCanonicalSubNodes)]
            } else {
                // Otherwise, define the canonical cell
                withCanonicalSubNodes
            }
        }
    }

    /**
     * Computes the next generation for the given [MacroCell.CellNode].
     *
     * For simplicity, this function will return a [MacroCell.CellNode] that is half as big, centered on this node.
     * (in other words, a [MacroCell.CellNode] with a decremented level).
     *
     * This function is memoized by [cellMap].
     *
     * @param useMap if true, use the [canonicalCellMap] to memoize the answer. If false,
     */
    @Suppress("LongMethod", "ComplexMethod")
    private fun MacroCell.CellNode.computeNextGeneration(
        useMap: Boolean = true,
    ): MacroCell.CellNode {
        require(level >= 2)

        // Ensure we are operating upon a canonical macro cell
        val canonicalMacroCell = makeCanonical()
        if (useMap) {
            return cellMap[CanonicalMacroCellEquivalence.wrap(canonicalMacroCell)]
        }

        val nw = canonicalMacroCell.nw as MacroCell.CellNode
        val ne = canonicalMacroCell.ne as MacroCell.CellNode
        val sw = canonicalMacroCell.sw as MacroCell.CellNode
        val se = canonicalMacroCell.se as MacroCell.CellNode

        return if (level == 2) {
            nw.nw as MacroCell.Cell
            nw.ne as MacroCell.Cell
            nw.sw as MacroCell.Cell
            nw.se as MacroCell.Cell
            ne.nw as MacroCell.Cell
            ne.ne as MacroCell.Cell
            ne.sw as MacroCell.Cell
            ne.se as MacroCell.Cell
            sw.nw as MacroCell.Cell
            sw.ne as MacroCell.Cell
            sw.sw as MacroCell.Cell
            sw.se as MacroCell.Cell
            se.nw as MacroCell.Cell
            se.ne as MacroCell.Cell
            se.sw as MacroCell.Cell
            se.se as MacroCell.Cell

            val nwCount = listOf(
                nw.nw.isAlive,
                nw.ne.isAlive,
                ne.nw.isAlive,
                nw.sw.isAlive,
                ne.sw.isAlive,
                sw.nw.isAlive,
                sw.ne.isAlive,
                se.nw.isAlive,
            ).count { it }
            val newNw = when (nw.se) {
                MacroCell.Cell.AliveCell -> if (nwCount in 2..3) MacroCell.Cell.AliveCell else MacroCell.Cell.DeadCell
                MacroCell.Cell.DeadCell -> if (nwCount == 3) MacroCell.Cell.AliveCell else MacroCell.Cell.DeadCell
            }

            val neCount = listOf(
                nw.ne.isAlive,
                ne.nw.isAlive,
                ne.ne.isAlive,
                nw.se.isAlive,
                ne.se.isAlive,
                sw.ne.isAlive,
                se.nw.isAlive,
                se.ne.isAlive,
            ).count { it }
            val newNe = when (ne.sw) {
                MacroCell.Cell.AliveCell -> if (neCount in 2..3) MacroCell.Cell.AliveCell else MacroCell.Cell.DeadCell
                MacroCell.Cell.DeadCell -> if (neCount == 3) MacroCell.Cell.AliveCell else MacroCell.Cell.DeadCell
            }

            val swCount = listOf(
                nw.sw.isAlive,
                nw.se.isAlive,
                ne.sw.isAlive,
                sw.nw.isAlive,
                se.nw.isAlive,
                sw.sw.isAlive,
                sw.se.isAlive,
                se.sw.isAlive,
            ).count { it }
            val newSw = when (sw.ne) {
                MacroCell.Cell.AliveCell -> if (swCount in 2..3) MacroCell.Cell.AliveCell else MacroCell.Cell.DeadCell
                MacroCell.Cell.DeadCell -> if (swCount == 3) MacroCell.Cell.AliveCell else MacroCell.Cell.DeadCell
            }

            val seCount = listOf(
                nw.se.isAlive,
                ne.sw.isAlive,
                ne.se.isAlive,
                sw.ne.isAlive,
                se.ne.isAlive,
                sw.se.isAlive,
                se.sw.isAlive,
                se.se.isAlive,
            ).count { it }
            val newSe = when (se.nw) {
                MacroCell.Cell.AliveCell -> if (seCount in 2..3) MacroCell.Cell.AliveCell else MacroCell.Cell.DeadCell
                MacroCell.Cell.DeadCell -> if (seCount == 3) MacroCell.Cell.AliveCell else MacroCell.Cell.DeadCell
            }

            MacroCell.CellNode(
                nw = newNw,
                ne = newNe,
                sw = newSw,
                se = newSe,
            )
        } else {
            val n00 = centeredSubnode(nw)
            val n01 = centeredHorizontal(nw, ne)
            val n02 = centeredSubnode(ne)
            val n10 = centeredVertical(nw, sw)
            val n11 = centeredSubSubnode(canonicalMacroCell)
            val n12 = centeredVertical(ne, se)
            val n20 = centeredSubnode(sw)
            val n21 = centeredHorizontal(sw, se)
            val n22 = centeredSubnode(se)

            MacroCell.CellNode(
                nw = MacroCell.CellNode(
                    nw = n00,
                    ne = n01,
                    sw = n10,
                    se = n11,
                ).computeNextGeneration(),
                ne = MacroCell.CellNode(
                    nw = n01,
                    ne = n02,
                    sw = n11,
                    se = n12,
                ).computeNextGeneration(),
                sw = MacroCell.CellNode(
                    nw = n10,
                    ne = n11,
                    sw = n20,
                    se = n21,
                ).computeNextGeneration(),
                se = MacroCell.CellNode(
                    nw = n11,
                    ne = n12,
                    sw = n21,
                    se = n22,
                ).computeNextGeneration(),
            )
        }.makeCanonical()
    }

    override suspend fun computeGenerationWithStep(
        cellState: CellState,
        @IntRange(from = 0) step: Int,
    ): CellState =
        withContext(dispatchers.Default) {
            computeGenerationWithStepImpl(
                cellState = cellState.toHashLifeCellState(),
                step = step,
            )
        }

    private tailrec fun computeGenerationWithStepImpl(
        cellState: HashLifeCellState,
        @IntRange(from = 0) step: Int,
    ): HashLifeCellState =
        if (step == 0) {
            cellState
        } else {
            val nextGeneration = computeNextGeneration(cellState)
            computedGenerations++
            computeGenerationWithStepImpl(
                cellState = nextGeneration,
                step = step - 1,
            )
        }

    /**
     * Returns the [HashLifeCellState] corresponding to the next generation.
     */
    @Suppress("ComplexMethod")
    private tailrec fun computeNextGeneration(cellState: HashLifeCellState): HashLifeCellState {
        val node = cellState.macroCell as MacroCell.CellNode

        if (node.level > 3) {
            node.nw as MacroCell.CellNode
            node.nw.nw as MacroCell.CellNode
            node.nw.ne as MacroCell.CellNode
            node.nw.sw as MacroCell.CellNode
            node.nw.se as MacroCell.CellNode
            node.ne as MacroCell.CellNode
            node.ne.nw as MacroCell.CellNode
            node.ne.ne as MacroCell.CellNode
            node.ne.sw as MacroCell.CellNode
            node.ne.se as MacroCell.CellNode
            node.sw as MacroCell.CellNode
            node.sw.nw as MacroCell.CellNode
            node.sw.ne as MacroCell.CellNode
            node.sw.sw as MacroCell.CellNode
            node.sw.se as MacroCell.CellNode
            node.se as MacroCell.CellNode
            node.se.nw as MacroCell.CellNode
            node.se.ne as MacroCell.CellNode
            node.se.sw as MacroCell.CellNode
            node.se.se as MacroCell.CellNode

            @Suppress("ComplexCondition")
            if (node.nw.nw.size == 0 && node.nw.ne.size == 0 && node.nw.ne.size == 0 &&
                node.nw.se.nw.size == 0 && node.nw.se.ne.size == 0 && node.nw.se.sw.size == 0 &&
                node.ne.nw.size == 0 && node.ne.ne.size == 0 && node.ne.se.size == 0 &&
                node.ne.sw.nw.size == 0 && node.ne.sw.ne.size == 0 && node.ne.sw.se.size == 0 &&
                node.sw.nw.size == 0 && node.sw.sw.size == 0 && node.sw.se.size == 0 &&
                node.sw.ne.nw.size == 0 && node.sw.ne.sw.size == 0 && node.sw.ne.se.size == 0 &&
                node.se.ne.size == 0 && node.se.sw.size == 0 && node.se.se.size == 0 &&
                node.se.nw.ne.size == 0 && node.se.nw.sw.size == 0 && node.se.nw.se.size == 0
            ) {
                return HashLifeCellState(
                    offset = cellState.offset + IntOffset(1 shl (node.level - 2), 1 shl (node.level - 2)),
                    macroCell = cellState.macroCell.computeNextGeneration(),
                )
            }
        }

        // If our primary macro cell would be too small or the resulting macro cell wouldn't be the correct result
        // (due to an expanding pattern), expand the main macro cell and compute.
        return computeNextGeneration(cellState.expandCentered())
    }
}

private fun centeredSubnode(node: MacroCell.CellNode): MacroCell.CellNode {
    require(node.level >= 2)
    node.nw as MacroCell.CellNode
    node.ne as MacroCell.CellNode
    node.sw as MacroCell.CellNode
    node.se as MacroCell.CellNode
    return MacroCell.CellNode(
        nw = node.nw.se,
        ne = node.ne.sw,
        sw = node.sw.ne,
        se = node.se.nw,
    )
}

private fun centeredHorizontal(w: MacroCell.CellNode, e: MacroCell.CellNode): MacroCell.CellNode {
    require(w.level >= 2)
    require(e.level >= 2)
    w.ne as MacroCell.CellNode
    w.se as MacroCell.CellNode
    e.nw as MacroCell.CellNode
    e.sw as MacroCell.CellNode
    return MacroCell.CellNode(
        nw = w.ne.se,
        ne = e.nw.sw,
        sw = w.se.ne,
        se = e.sw.nw,
    )
}

private fun centeredVertical(n: MacroCell.CellNode, s: MacroCell.CellNode): MacroCell.CellNode {
    require(n.level >= 2)
    require(s.level >= 2)
    n.se as MacroCell.CellNode
    n.sw as MacroCell.CellNode
    s.nw as MacroCell.CellNode
    s.ne as MacroCell.CellNode
    return MacroCell.CellNode(
        nw = n.sw.se,
        ne = n.se.sw,
        sw = s.nw.ne,
        se = s.ne.nw,
    )
}

private fun centeredSubSubnode(node: MacroCell.CellNode): MacroCell.CellNode {
    require(node.level >= 3)
    node.nw as MacroCell.CellNode
    node.ne as MacroCell.CellNode
    node.sw as MacroCell.CellNode
    node.se as MacroCell.CellNode
    node.nw.se as MacroCell.CellNode
    node.ne.sw as MacroCell.CellNode
    node.sw.ne as MacroCell.CellNode
    node.se.nw as MacroCell.CellNode
    return MacroCell.CellNode(
        nw = node.nw.se.se,
        ne = node.ne.sw.sw,
        sw = node.sw.ne.ne,
        se = node.se.nw.nw,
    )
}

/**
 * An [Equivalence] describing a "canonical" [MacroCell.CellNode].
 *
 * For the purposes of efficient hashing of computations, we want to ensure that the computation of the next
 * generation for each [MacroCell.CellNode] is only done once, and cached.
 *
 * Two different instances of [MacroCell.CellNode] could be equal, but determining that would require traversing the
 * whole tree, which is too slow.
 *
 * Therefore, we define the notion of a "canonical" cell node for a [HashLifeAlgorithm] instance as follows:
 * - A leaf [MacroCell.Cell] is automatically canonical, since only two such objects exist:
 *   [MacroCell.Cell.AliveCell] and [MacroCell.Cell.DeadCell]
 * - A non-leaf [MacroCell.CellNode] is canonical if all of its subnodes are canonical, and any [MacroCell.CellNode]
 *   subnodes are stored in [HashLifeAlgorithm.canonicalCellMap].
 *
 * Using this convention, we can compute equality of canonical cell nodes in O(1) time, by using referential equality
 * of the subnodes.
 */
private object CanonicalMacroCellEquivalence : Equivalence<MacroCell.CellNode>() {
    override fun doEquivalent(a: MacroCell.CellNode, b: MacroCell.CellNode): Boolean =
        a.level == b.level && a.nw === b.nw && a.ne === b.ne && a.sw === b.sw && a.se === b.se

    override fun doHash(t: MacroCell.CellNode): Int = t.hashCode()
}
