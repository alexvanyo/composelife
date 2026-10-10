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
import com.alexvanyo.composelife.model.f_Algorithm_makeCanonicalCellNodeWith
import com.alexvanyo.composelife.model.f_Algorithm_prepareStep
import com.alexvanyo.composelife.model.f_Algorithm_stepCellNodeWith
import com.alexvanyo.composelife.model.toHashLifeCellState
import com.alexvanyo.composelife.tracing.Tracer
import com.alexvanyo.composelife.tracing.trace
import com.alexvanyo.composelife.tracing.traceCoroutine
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
    private val tracer: Tracer,
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
    private val canonicalCellNodeMap: Cache<Equivalence.Wrapper<MacroCell.CellNode>, MacroCell.CellNode> =
        Cache(
            load = { key -> key.value.makeCanonical(false) },
            getGenerationIndex = { computedGenerations },
        )

    private val canonicalLevel4NodeMap: Cache<MacroCell.Level4Node, MacroCell.Level4Node> =
        Cache(
            load = { key -> key.makeCanonical(false) },
            getGenerationIndex = { computedGenerations },
        )

    /**
     * The memoization map for [MacroCell.CellNode.computeNextGeneration].
     */
    private val cellNodeMap: Cache<Equivalence.Wrapper<MacroCell.CellNode>, MacroCell> =
        Cache(
            load = { key -> key.value.computeNextGeneration(false) },
            getGenerationIndex = { computedGenerations },
        )

    /**
     * The memoization map for [MacroCell.Level4Node.computeNextGeneration].
     */
    private val level4NodeMap: ObjectLongCache<MacroCell.Level4Node> =
        ObjectLongCache(
            load = { key ->
                computeLevel4NextGeneration(
                    node = key,
                    computeLeafNextGen = { it.computeNextGenerationMemoized() },
                )
            },
            getGenerationIndex = { computedGenerations },
        )

    /**
     * The memoization map for [MacroCell.LeafNode.computeNextGeneration].
     */
    private val leafNodeMap: LongIntCache =
        LongIntCache(
            load = { key -> key.computeNextGeneration() },
            getGenerationIndex = { computedGenerations },
        )

    private fun MacroCell.makeCanonical(useMap: Boolean = true): MacroCell = tracer.trace(
        category = "HashLifeAlgorithm",
        name = "makeCanonical",
    ) {
        when (this) {
            is MacroCell.Level4Node -> makeCanonical(useMap)
            is MacroCell.CellNode -> makeCanonical(useMap)
        }
    }

    private fun MacroCell.Level4Node.makeCanonical(useMap: Boolean = true): MacroCell.Level4Node = if (useMap) {
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
            val withCanonicalSubNodes =
                f_Algorithm_makeCanonicalCellNodeWith(this) { it.makeCanonical() } as MacroCell.CellNode

            if (useMap) {
                // If we're using the map, pull from it now with canonical cell nodes
                canonicalCellNodeMap[canonicalCellNodeEquivalence.wrap(withCanonicalSubNodes)]
            } else {
                // Otherwise, define the canonical cell
                withCanonicalSubNodes
            }
        }
    }

    private fun MacroCell.Level4Node.computeNextGeneration(useMap: Boolean = true): LeafNode = tracer.trace(
        category = "HashLifeAlgorithm",
        name = "Level4Node.computeNextGeneration",
    ) {
        // Ensure we are operating upon a canonical macro cell
        val canonicalMacroCell = makeCanonical()
        if (useMap) {
            return@trace level4NodeMap[canonicalMacroCell]
        }

        computeLevel4NextGeneration(canonicalMacroCell)
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
    private fun MacroCell.CellNode.computeNextGeneration(useMap: Boolean = true): MacroCell = tracer.trace(
        category = "HashLifeAlgorithm",
        name = "CellNode.computeNextGeneration",
    ) {
        // Ensure we are operating upon a canonical macro cell
        val canonicalMacroCell = makeCanonical()
        if (useMap) {
            return@trace cellNodeMap[canonicalCellNodeEquivalence.wrap(canonicalMacroCell)]
        }

        f_Algorithm_stepCellNodeWith(
            canonicalMacroCell,
            stepLevel4 = { (it as MacroCell.Level4Node).computeNextGeneration() },
            stepCell = { (it as MacroCell.CellNode).computeNextGeneration() },
        ).makeCanonical()
    }

    /**
     * Computes the 4x4 [UShort] next generation for the given 8x8 [LeafNode] in its center.
     */
    private fun LeafNode.computeNextGenerationMemoized(): Int = leafNodeMap[this]

    override suspend fun computeGenerationWithStep(cellState: CellState, @IntRange(from = 0) step: Int): CellState =
        tracer.traceCoroutine(
            category = "HashLifeAlgorithm",
            name = "computeGenerationWithStep",
        ) {
            withContext(dispatchers.Default) {
                mutex.withLock {
                    computeGenerationWithStepImpl(
                        cellState = cellState.toHashLifeCellState(),
                        step = step,
                    )
                }
            }
        }

    private tailrec fun computeGenerationWithStepImpl(
        cellState: HashLifeCellState,
        @IntRange(from = 0) step: Int,
    ): HashLifeCellState = if (step == 0) {
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
    private fun computeNextGeneration(cellState: HashLifeCellState): HashLifeCellState = tracer.trace(
        category = "HashLifeAlgorithm",
        name = "computeNextGeneration",
    ) {
        computeNextGenerationImpl(cellState)
    }

    private fun computeNextGenerationImpl(cellState: HashLifeCellState): HashLifeCellState {
        val prep = f_Algorithm_prepareStep(cellState.macroCell)
        val delta = prep.offsetDelta
        return HashLifeCellState(
            offset = cellState.offset + IntOffset(delta, delta),
            macroCell = (prep.macroCell as MacroCell.CellNode).computeNextGeneration(),
        )
    }
}

private fun interface Equivalence<in T> {
    fun isEquivalent(a: T, b: T): Boolean

    fun hash(value: T): Int = value.hashCode()

    class Wrapper<T>(private val equivalence: Equivalence<T>, val value: T) {
        @Suppress("UNCHECKED_CAST")
        override fun equals(other: Any?): Boolean = other is Wrapper<*> &&
            other.equivalence === equivalence &&
            equivalence.isEquivalent(value, (other as Wrapper<T>).value)

        override fun hashCode(): Int = equivalence.hash(value)
    }
}

private fun <T> Equivalence<T>.wrap(value: T): Equivalence.Wrapper<T> = Equivalence.Wrapper(this, value)

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
        a.level() == b.level() && a.nw === b.nw && a.ne === b.ne && a.sw === b.sw && a.se === b.se
    }

private class Cache<K, V>(private val load: (K) -> V, private val getGenerationIndex: () -> Long) {
    private val mutableMap: MutableMap<K, V> = mutableMapOf()
    val map: Map<K, V> get() = mutableMap

    private val lastAccessedGenerationMap: MutableMap<K, Long> = mutableMapOf()

    operator fun get(key: K): V = mutableMap.getOrPut(key) { load(key) }.also {
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

private class ObjectLongCache<K>(private val load: (K) -> ULong, private val getGenerationIndex: () -> Long) {
    private val mutableMap: MutableObjectLongMap<K> = mutableObjectLongMapOf()
    val map: ObjectLongMap<K> get() = mutableMap

    private val lastAccessedGenerationMap: MutableObjectLongMap<K> = mutableObjectLongMapOf()

    operator fun get(key: K): ULong = mutableMap.getOrPut(key) { load(key).toLong() }.toULong().also {
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

private class LongIntCache(private val load: (ULong) -> Int, private val getGenerationIndex: () -> Long) {
    private val mutableMap: MutableLongIntMap = mutableLongIntMapOf()
    val map: LongIntMap get() = mutableMap

    private val lastAccessedGenerationMap: MutableLongLongMap = mutableLongLongMapOf()

    operator fun get(key: ULong): Int = mutableMap.getOrPut(key.toLong()) { load(key) }.also {
        lastAccessedGenerationMap[key.toLong()] = getGenerationIndex()
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
