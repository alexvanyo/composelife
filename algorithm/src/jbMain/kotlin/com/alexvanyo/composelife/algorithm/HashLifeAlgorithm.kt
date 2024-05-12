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
@file:Suppress("TooManyFunctions", "NOTHING_TO_INLINE")

package com.alexvanyo.composelife.algorithm

import androidx.annotation.IntRange
import androidx.collection.LongIntMap
import androidx.collection.MutableLongIntMap
import androidx.collection.MutableLongLongMap
import androidx.collection.MutableObjectLongMap
import androidx.collection.ObjectLongMap
import androidx.collection.mutableLongIntMapOf
import androidx.collection.mutableLongLongMapOf
import androidx.collection.mutableObjectLongMapOf
import androidx.compose.ui.unit.IntOffset
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.model.HashLifeCellState
import com.alexvanyo.composelife.model.LeafNode
import com.alexvanyo.composelife.model.MacroCell
import com.alexvanyo.composelife.model.expandCentered
import com.alexvanyo.composelife.model.ne
import com.alexvanyo.composelife.model.nw
import com.alexvanyo.composelife.model.se
import com.alexvanyo.composelife.model.size
import com.alexvanyo.composelife.model.sw
import com.alexvanyo.composelife.model.toHashLifeCellState
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.Inject
import dev.zacsweers.metro.SingleIn
import kotlinx.coroutines.sync.Mutex
import kotlinx.coroutines.sync.withLock
import kotlinx.coroutines.withContext
import kotlin.collections.iterator
import kotlin.collections.set

@SingleIn(AppScope::class)
@Inject
class HashLifeAlgorithm(
    private val dispatchers: ComposeLifeDispatchers,
    private val generationsToCacheInMacroCellMaps: Int = 256,
    private val generationsToCacheInLeafNodeMap: Int = 1024,
) : GameOfLifeAlgorithm {

    private val mutex = Mutex()

    /**
     * The current number of computed generations.
     *
     * Note this does not have any direct relation to the current generation count of a specific genealogy, since
     * this same instance can be used to compute multiple genealogies.
     *
     * This value is used to prune the caches of [canonicalCellNodeMap], [cellNodeMap] and [leafNodeMap].
     */
    private var computedGenerations = 0L

    /**
     * The map containing the "canonical" [MacroCell.CellNode]s. This ensures that there is exactly one instance of
     * each equivalent [MacroCell.CellNode] (which makes comparing [MacroCell.CellNode]s possible in O(1) with just
     * reference checking).
     *
     * The keys of this map must already have canonical subnodes, which is ensured by the implementation of
     * [makeCanonical].
     */
    private val canonicalCellNodeMap: Cache<Equivalence.Wrapper<MacroCell.CellNode>, MacroCell.CellNode> = Cache(
        load = { key -> key.value.makeCanonical(false) },
        getGenerationIndex = { computedGenerations },
    )

    private val canonicalLevel4NodeMap: Cache<MacroCell.Level4Node, MacroCell.Level4Node> = Cache(
        load = { key -> key.makeCanonical(false) },
        getGenerationIndex = { computedGenerations },
    )

    /**
     * The memoization map for [MacroCell.CellNode.computeNextGeneration].
     */
    private val cellNodeMap: Cache<Equivalence.Wrapper<MacroCell.CellNode>, MacroCell> = Cache(
        load = { key -> key.value.computeNextGeneration(false) },
        getGenerationIndex = { computedGenerations },
    )

    /**
     * The memoization map for [MacroCell.Level4Node.computeNextGeneration].
     */
    private val level4NodeMap: ObjectLongCache<MacroCell.Level4Node> =
        ObjectLongCache(
            load = { key -> key.computeNextGeneration(false) },
            getGenerationIndex = { computedGenerations },
        )

    /**
     * The memoization map for [MacroCell.LeafNode.computeNextGeneration].
     */
    private val leafNodeMap: LongIntCache = LongIntCache(
        load = { key -> key.computeNextGeneration() },
        getGenerationIndex = { computedGenerations },
    )

    private fun MacroCell.makeCanonical(useMap: Boolean = true): MacroCell =
        when (this) {
            is MacroCell.Level4Node -> makeCanonical(useMap)
            is MacroCell.CellNode -> makeCanonical(useMap)
        }

    private fun MacroCell.Level4Node.makeCanonical(useMap: Boolean = true): MacroCell.Level4Node =
        if (useMap) {
            // If we're using the map, pull from it now
            canonicalLevel4NodeMap[this]
        } else {
            // Otherwise, define the canonical cell
            this
        }

    private fun MacroCell.CellNode.makeCanonical(useMap: Boolean = true): MacroCell.CellNode {
        val currentEntry = canonicalCellNodeMap.map[canonicalCellNodeEquivalence.wrap(this)]

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
                canonicalCellNodeMap[canonicalCellNodeEquivalence.wrap(withCanonicalSubNodes)]
            } else {
                // Otherwise, define the canonical cell
                withCanonicalSubNodes
            }
        }
    }

    private fun MacroCell.Level4Node.computeNextGeneration(
        useMap: Boolean = true,
    ): MacroCell.LeafNode {
        // Ensure we are operating upon a canonical macro cell
        val canonicalMacroCell = makeCanonical()
        if (useMap) {
            return level4NodeMap[canonicalMacroCell]
        }

        val n00 = centeredSubnodeLevel3(nw)
        val n01 = centeredHorizontalSubnodeLevel3(nw, ne)
        val n02 = centeredSubnodeLevel3(ne)
        val n10 = centeredVerticalSubnodeLevel3(nw, sw)
        val n11 = centeredSubSubnodeLevel4(canonicalMacroCell)
        val n12 = centeredVerticalSubnodeLevel3(ne, se)
        val n20 = centeredSubnodeLevel3(sw)
        val n21 = centeredHorizontalSubnodeLevel3(sw, se)
        val n22 = centeredSubnodeLevel3(se)

        return LeafNode(
            nw = LeafNode(
                nw = n00,
                ne = n01,
                sw = n10,
                se = n11,
            ).computeNextGenerationMemoized(),
            ne = LeafNode(
                nw = n01,
                ne = n02,
                sw = n11,
                se = n12,
            ).computeNextGenerationMemoized(),
            sw = LeafNode(
                nw = n10,
                ne = n11,
                sw = n20,
                se = n21,
            ).computeNextGenerationMemoized(),
            se = LeafNode(
                nw = n11,
                ne = n12,
                sw = n21,
                se = n22,
            ).computeNextGenerationMemoized(),
        )
    }

    /**
     * Computes the next generation for the given [MacroCell.CellNode].
     *
     * For simplicity, this function will return a [MacroCell.CellNode] that is half as big, centered on this node.
     * (in other words, a [MacroCell.CellNode] with a decremented level).
     *
     * This function is memoized by [cellNodeMap].
     *
     * @param useMap if true, use the [cellNodeMap] to memoize the answer.
     */
    @Suppress("LongMethod", "ComplexMethod")
    private fun MacroCell.CellNode.computeNextGeneration(
        useMap: Boolean = true,
    ): MacroCell {
        // Ensure we are operating upon a canonical macro cell
        val canonicalMacroCell = makeCanonical()
        if (useMap) {
            return cellNodeMap[canonicalCellNodeEquivalence.wrap(canonicalMacroCell)]
        }

        return when (level) {
            5 -> {
                nw as MacroCell.Level4Node
                ne as MacroCell.Level4Node
                sw as MacroCell.Level4Node
                se as MacroCell.Level4Node

                val n00 = centeredSubnodeLevel4(nw)
                val n01 = centeredHorizontalSubnodeLevel4(nw, ne)
                val n02 = centeredSubnodeLevel4(ne)
                val n10 = centeredVerticalSubnodeLevel4(nw, sw)
                val n11 = centeredSubSubnodeLevel5(canonicalMacroCell)
                val n12 = centeredVerticalSubnodeLevel4(ne, se)
                val n20 = centeredSubnodeLevel4(sw)
                val n21 = centeredHorizontalSubnodeLevel4(sw, se)
                val n22 = centeredSubnodeLevel4(se)

                MacroCell.Level4Node(
                    nw = MacroCell.Level4Node(
                        nw = n00,
                        ne = n01,
                        sw = n10,
                        se = n11,
                    ).computeNextGeneration(),
                    ne = MacroCell.Level4Node(
                        nw = n01,
                        ne = n02,
                        sw = n11,
                        se = n12,
                    ).computeNextGeneration(),
                    sw = MacroCell.Level4Node(
                        nw = n10,
                        ne = n11,
                        sw = n20,
                        se = n21,
                    ).computeNextGeneration(),
                    se = MacroCell.Level4Node(
                        nw = n11,
                        ne = n12,
                        sw = n21,
                        se = n22,
                    ).computeNextGeneration(),
                )
            }
            6 -> {
                nw as MacroCell.CellNode
                ne as MacroCell.CellNode
                sw as MacroCell.CellNode
                se as MacroCell.CellNode

                val n00 = centeredSubnodeLevel5(nw)
                val n01 = centeredHorizontalSubnodeLevel5(nw, ne)
                val n02 = centeredSubnodeLevel5(ne)
                val n10 = centeredVerticalSubnodeLevel5(nw, sw)
                val n11 = centeredSubSubnodeLevel6(canonicalMacroCell)
                val n12 = centeredVerticalSubnodeLevel5(ne, se)
                val n20 = centeredSubnodeLevel5(sw)
                val n21 = centeredHorizontalSubnodeLevel5(sw, se)
                val n22 = centeredSubnodeLevel5(se)

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
            }
            else -> {
                nw as MacroCell.CellNode
                ne as MacroCell.CellNode
                sw as MacroCell.CellNode
                se as MacroCell.CellNode

                val n00 = centeredSubnodeLevel6(nw)
                val n01 = centeredHorizontalSubnodeLevel6(nw, ne)
                val n02 = centeredSubnodeLevel6(ne)
                val n10 = centeredVerticalSubnodeLevel6(nw, sw)
                val n11 = centeredSubSubnodeLevel7(canonicalMacroCell)
                val n12 = centeredVerticalSubnodeLevel6(ne, se)
                val n20 = centeredSubnodeLevel6(sw)
                val n21 = centeredHorizontalSubnodeLevel6(sw, se)
                val n22 = centeredSubnodeLevel6(se)

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
            }
        }.makeCanonical()
    }

    /**
     * Computes the 4x4 [UShort] next generation for the given 8x8 [MacroCell.LeafNode] in its center.
     */
    private fun MacroCell.LeafNode.computeNextGenerationMemoized(): Int =
        leafNodeMap[this]

    override suspend fun computeGenerationWithStep(
        cellState: CellState,
        @IntRange(from = 0) step: Int,
    ): CellState =
        withContext(dispatchers.Default) {
            mutex.withLock {
                computeGenerationWithStepImpl(
                    cellState = cellState.toHashLifeCellState(),
                    step = step,
                )
            }
        }

    private tailrec fun computeGenerationWithStepImpl(
        cellState: HashLifeCellState,
        @IntRange(from = 0) step: Int,
    ): HashLifeCellState =
        if (step == 0) {
            val oldestGenerationToKeepInMacroCellMaps = computedGenerations - generationsToCacheInMacroCellMaps
            canonicalCellNodeMap.prune(oldestGenerationToKeepInMacroCellMaps)
            canonicalLevel4NodeMap.prune(oldestGenerationToKeepInMacroCellMaps)
            cellNodeMap.prune(oldestGenerationToKeepInMacroCellMaps)
            level4NodeMap.prune(oldestGenerationToKeepInMacroCellMaps)
            val oldestGenerationToKeepInLeafNodeMap = computedGenerations - generationsToCacheInLeafNodeMap
            leafNodeMap.prune(oldestGenerationToKeepInLeafNodeMap)
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
    private tailrec fun computeNextGeneration(cellState: HashLifeCellState): HashLifeCellState {
        val node = cellState.macroCell
        val needToExpand = node.level <= 4 || when (node) {
            is MacroCell.CellNode -> {
                when (node.level) {
                    5 -> centeredSubSubnodeLevel5(node).size
                    6 -> centeredSubSubnodeLevel6(node).size
                    else -> centeredSubSubnodeLevel7(node).size
                }
            }
            is MacroCell.Level4Node -> error("Impossible, since level is larger than 4")
        } != node.size

        if (!needToExpand) {
            return HashLifeCellState(
                offset = cellState.offset + IntOffset(1 shl (node.level - 2), 1 shl (node.level - 2)),
                macroCell = node.computeNextGeneration(),
            )
        }

        // If our primary macro cell would be too small or the resulting macro cell wouldn't be the correct result
        // (due to an expanding pattern), expand the main macro cell and compute.
        return computeNextGeneration(cellState.expandCentered())
    }
}

private inline fun centeredSubnodeLevel6(node: MacroCell.CellNode): MacroCell.CellNode {
    // require(node.level >= 6)
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

private inline fun centeredSubnodeLevel5(node: MacroCell.CellNode): MacroCell.Level4Node {
    node.nw as MacroCell.Level4Node
    node.ne as MacroCell.Level4Node
    node.sw as MacroCell.Level4Node
    node.se as MacroCell.Level4Node
    return MacroCell.Level4Node(
        nw = node.nw.se,
        ne = node.ne.sw,
        sw = node.sw.ne,
        se = node.se.nw,
    )
}

private inline fun centeredSubnodeLevel4(node: MacroCell.Level4Node): MacroCell.LeafNode =
    LeafNode(
        nw = node.nw.se,
        ne = node.ne.sw,
        sw = node.sw.ne,
        se = node.se.nw,
    )

private inline fun centeredSubnodeLevel3(node: MacroCell.LeafNode): Int =
    node.nw.se +
        node.ne.sw * 16 +
        node.sw.ne * 16 * 16 +
        node.se.nw * 16 * 16 * 16

private inline fun centeredHorizontalSubnodeLevel6(w: MacroCell.CellNode, e: MacroCell.CellNode): MacroCell.CellNode {
    // require(e.level >= 6)
    // require(e.level == w.level)
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

private inline fun centeredHorizontalSubnodeLevel5(w: MacroCell.CellNode, e: MacroCell.CellNode): MacroCell.Level4Node {
    // require(e.level == 5)
    // require(e.level == w.level)
    w.ne as MacroCell.Level4Node
    w.se as MacroCell.Level4Node
    e.nw as MacroCell.Level4Node
    e.sw as MacroCell.Level4Node
    return MacroCell.Level4Node(
        nw = w.ne.se,
        ne = e.nw.sw,
        sw = w.se.ne,
        se = e.sw.nw,
    )
}

private inline fun centeredHorizontalSubnodeLevel4(
    w: MacroCell.Level4Node,
    e: MacroCell.Level4Node,
): MacroCell.LeafNode =
    LeafNode(
        nw = w.ne.se,
        ne = e.nw.sw,
        sw = w.se.ne,
        se = e.sw.nw,
    )

private inline fun centeredHorizontalSubnodeLevel3(w: MacroCell.LeafNode, e: MacroCell.LeafNode): Int =
    w.ne.se +
        e.nw.sw * 16 +
        w.se.ne * 16 * 16 +
        e.sw.nw * 16 * 16 * 16

private inline fun centeredVerticalSubnodeLevel6(n: MacroCell.CellNode, s: MacroCell.CellNode): MacroCell.CellNode {
    // require(n.level >= 6)
    // require(s.level == n.level)
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

private inline fun centeredVerticalSubnodeLevel5(n: MacroCell.CellNode, s: MacroCell.CellNode): MacroCell.Level4Node {
    // require(n.level == 5)
    // require(s.level == n.level)
    n.se as MacroCell.Level4Node
    n.sw as MacroCell.Level4Node
    s.nw as MacroCell.Level4Node
    s.ne as MacroCell.Level4Node
    return MacroCell.Level4Node(
        nw = n.sw.se,
        ne = n.se.sw,
        sw = s.nw.ne,
        se = s.ne.nw,
    )
}

private inline fun centeredVerticalSubnodeLevel4(n: MacroCell.Level4Node, s: MacroCell.Level4Node): MacroCell.LeafNode =
    LeafNode(
        nw = n.sw.se,
        ne = n.se.sw,
        sw = s.nw.ne,
        se = s.ne.nw,
    )

private inline fun centeredVerticalSubnodeLevel3(n: MacroCell.LeafNode, s: MacroCell.LeafNode): Int =
    n.sw.se +
        n.se.sw * 16 +
        s.nw.ne * 16 * 16 +
        s.ne.nw * 16 * 16 * 16

private inline fun centeredSubSubnodeLevel7(node: MacroCell.CellNode): MacroCell.CellNode {
    // require(node.level >= 7)
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

private inline fun centeredSubSubnodeLevel6(node: MacroCell.CellNode): MacroCell.Level4Node {
    // require(node.level == 6)
    node.nw as MacroCell.CellNode
    node.ne as MacroCell.CellNode
    node.sw as MacroCell.CellNode
    node.se as MacroCell.CellNode
    node.nw.se as MacroCell.Level4Node
    node.ne.sw as MacroCell.Level4Node
    node.sw.ne as MacroCell.Level4Node
    node.se.nw as MacroCell.Level4Node
    return MacroCell.Level4Node(
        nw = node.nw.se.se,
        ne = node.ne.sw.sw,
        sw = node.sw.ne.ne,
        se = node.se.nw.nw,
    )
}

private inline fun centeredSubSubnodeLevel5(node: MacroCell.CellNode): MacroCell.LeafNode {
    // require(node.level == 5)
    node.nw as MacroCell.Level4Node
    node.ne as MacroCell.Level4Node
    node.sw as MacroCell.Level4Node
    node.se as MacroCell.Level4Node
    return LeafNode(
        nw = node.nw.se.se,
        ne = node.ne.sw.sw,
        sw = node.sw.ne.ne,
        se = node.se.nw.nw,
    )
}

private inline fun centeredSubSubnodeLevel4(node: MacroCell.Level4Node): Int =
    node.nw.se.se +
        node.ne.sw.sw * 16 +
        node.sw.ne.ne * 16 * 16 +
        node.se.nw.nw * 16 * 16 * 16

private fun interface Equivalence<in T> {

    fun isEquivalent(a: T, b: T): Boolean

    fun hash(value: T): Int = value.hashCode()

    class Wrapper<T>(
        private val equivalence: Equivalence<T>,
        val value: T,
    ) {
        @Suppress("UNCHECKED_CAST")
        override fun equals(other: Any?): Boolean =
            other is Wrapper<*> &&
                other.equivalence === equivalence &&
                equivalence.isEquivalent(value, (other as Wrapper<T>).value)

        override fun hashCode(): Int = equivalence.hash(value)
    }
}

private fun <T> Equivalence<T>.wrap(value: T): Equivalence.Wrapper<T> =
    Equivalence.Wrapper(this, value)

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
 * - A leaf [MacroCell.LeafNode] is automatically canonical, since they are represented as just a [ULong] value class.
 * - A non-leaf [MacroCell.CellNode] is canonical if all of its subnodes are canonical, and any [MacroCell.CellNode]
 *   subnodes are stored in [HashLifeAlgorithm.canonicalCellNodeMap].
 *
 * Using this convention, we can compute equality of canonical cell nodes in O(1) time, by using referential equality
 * of the subnodes.
 */
private val canonicalCellNodeEquivalence: Equivalence<MacroCell.CellNode> =
    Equivalence { a: MacroCell.CellNode, b: MacroCell.CellNode ->
        a.level == b.level && a.nw === b.nw && a.ne === b.ne && a.sw === b.sw && a.se === b.se
    }

private class Cache<K, V>(
    private val load: (K) -> V,
    private val getGenerationIndex: () -> Long,
) {
    private val mutableMap: MutableMap<K, V> = mutableMapOf()
    val map: Map<K, V> get() = mutableMap

    private val lastAccessedGenerationMap: MutableMap<K, Long> = mutableMapOf()

    operator fun get(key: K): V =
        mutableMap.getOrPut(key) { load(key) }.also {
            lastAccessedGenerationMap[key] = getGenerationIndex()
        }

    fun prune(oldestGenerationToKeep: Long) {
        val iterator = lastAccessedGenerationMap.iterator()
        while (iterator.hasNext()) {
            val mutableEntry = iterator.next()
            if (mutableEntry.value < oldestGenerationToKeep) {
                mutableMap.remove(mutableEntry.key)
                iterator.remove()
            }
        }
    }
}

private class ObjectLongCache<K>(
    private val load: (K) -> Long,
    private val getGenerationIndex: () -> Long,
) {
    private val mutableMap: MutableObjectLongMap<K> = mutableObjectLongMapOf()
    val map: ObjectLongMap<K> get() = mutableMap

    private val lastAccessedGenerationMap: MutableObjectLongMap<K> = mutableObjectLongMapOf()

    operator fun get(key: K): Long =
        mutableMap.getOrPut(key) { load(key) }.also {
            lastAccessedGenerationMap[key] = getGenerationIndex()
        }

    fun prune(oldestGenerationToKeep: Long) {
        lastAccessedGenerationMap.removeIf { key, value ->
            (value < oldestGenerationToKeep).also {
                if (it) {
                    mutableMap.remove(key)
                }
            }
        }
    }
}

private class LongIntCache(
    private val load: (Long) -> Int,
    private val getGenerationIndex: () -> Long,
) {
    private val mutableMap: MutableLongIntMap = mutableLongIntMapOf()
    val map: LongIntMap get() = mutableMap

    private val lastAccessedGenerationMap: MutableLongLongMap = mutableLongLongMapOf()

    operator fun get(key: Long): Int =
        mutableMap.getOrPut(key) { load(key) }.also {
            lastAccessedGenerationMap[key] = getGenerationIndex()
        }

    fun prune(oldestGenerationToKeep: Long) {
        lastAccessedGenerationMap.removeIf { key, value ->
            (value < oldestGenerationToKeep).also {
                if (it) {
                    mutableMap.remove(key)
                }
            }
        }
    }
}
