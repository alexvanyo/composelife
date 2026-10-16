/*
 * Copyright 2026 The Android Open Source Project
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
import androidx.compose.ui.unit.IntOffset
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.model.HashLifeCellState
import com.alexvanyo.composelife.model.HashLifeStepState
import com.alexvanyo.composelife.model.LeafNode
import com.alexvanyo.composelife.model.MacroCell
import com.alexvanyo.composelife.model.f_Algorithm_canonicalizeMacroCellWith
import com.alexvanyo.composelife.model.f_Algorithm_computeGenerationStep
import com.alexvanyo.composelife.model.f_Algorithm_stepCellNodeWith
import com.alexvanyo.composelife.model.f_Algorithm_stepHashLifeStateWith
import com.alexvanyo.composelife.model.f_Algorithm_stepLevel4Node
import com.alexvanyo.composelife.model.f_Algorithm_stepLevel4NodeWith
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
class LeanHashLifeAlgorithm(
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

    private val cellNodeQueryWrapper = Equivalence.ReusableWrapper(canonicalCellNodeEquivalence)

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
            load = { key -> key.value },
            getGenerationIndex = { computedGenerations },
        )

    private val canonicalLevel4NodeMap: Cache<MacroCell.Level4Node, MacroCell.Level4Node> =
        Cache(
            load = { key -> key },
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

    private val internLevel4Lambda: (MacroCell) -> MacroCell =
        { canonicalLevel4NodeMap[it as MacroCell.Level4Node] }
    private val findExistingCellLambda: (MacroCell) -> MacroCell? =
        { canonicalCellNodeMap.map[cellNodeQueryWrapper.set(it as MacroCell.CellNode)] }
    private val canonicalizeSubnodeLambda: (MacroCell) -> MacroCell =
        { it.makeCanonical() }
    private val internCellLambda: (MacroCell) -> MacroCell = {
        val cell = it as MacroCell.CellNode
        canonicalCellNodeMap.getWithQuery(cellNodeQueryWrapper.set(cell)) {
            cellNodeQueryWrapper.toPermanentWrapper()
        }
    }

    private val stepLevel4Lambda: (MacroCell) -> ULong =
        { (it as MacroCell.Level4Node).computeNextGeneration() }
    private val stepCellLambda: (MacroCell) -> MacroCell =
        { (it as MacroCell.CellNode).computeNextGeneration() }
    private val computeLeafMemoizedLambda: (ULong) -> UInt =
        { it.computeNextGenerationMemoized().toUInt() }

    /**
     * The memoization map for [MacroCell.Level4Node.computeNextGeneration].
     */
    private val level4NodeMap: ObjectLongCache<MacroCell.Level4Node> =
        ObjectLongCache(
            load = { key ->
                f_Algorithm_stepLevel4NodeWith(key, computeLeafMemoizedLambda)
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

    private fun MacroCell.makeCanonical(useMap: Boolean = true): MacroCell = if (!useMap) {
        this
    } else {
        f_Algorithm_canonicalizeMacroCellWith(
            m = this,
            internLevel4 = internLevel4Lambda,
            findExistingCell = findExistingCellLambda,
            canonicalizeSubnode = canonicalizeSubnodeLambda,
            internCell = internCellLambda,
        )
    }

    private fun MacroCell.Level4Node.computeNextGeneration(useMap: Boolean = true): LeafNode = tracer.trace(
        category = "LeanHashLifeAlgorithm",
        name = "Level4Node.computeNextGeneration",
    ) {
        // Ensure we are operating upon a canonical macro cell
        val canonicalMacroCell = makeCanonical(useMap) as MacroCell.Level4Node
        if (useMap) {
            return@trace level4NodeMap[canonicalMacroCell]
        }

        f_Algorithm_stepLevel4Node(canonicalMacroCell)
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
        category = "LeanHashLifeAlgorithm",
        name = "CellNode.computeNextGeneration",
    ) {
        // Ensure we are operating upon a canonical macro cell
        val canonicalMacroCell = makeCanonical(useMap) as MacroCell.CellNode
        if (useMap) {
            return@trace cellNodeMap.getWithQuery(cellNodeQueryWrapper.set(canonicalMacroCell)) {
                cellNodeQueryWrapper.toPermanentWrapper()
            }
        }

        f_Algorithm_stepCellNodeWith(
            canonicalMacroCell,
            stepLevel4 = stepLevel4Lambda,
            stepCell = stepCellLambda,
        ).makeCanonical()
    }

    /**
     * Computes the 4x4 [UShort] next generation for the given 8x8 [LeafNode] in its center.
     */
    private fun LeafNode.computeNextGenerationMemoized(): Int = leafNodeMap[this]

    override suspend fun computeGenerationWithStep(cellState: CellState, @IntRange(from = 0) step: Int): CellState =
        tracer.traceCoroutine(
            category = "LeanHashLifeAlgorithm",
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

    private fun stepPrepared(prepNode: MacroCell): MacroCell = f_Algorithm_stepCellNodeWith(
        m = prepNode,
        stepLevel4 = stepLevel4Lambda,
        stepCell = stepCellLambda,
    ).makeCanonical()

    private fun computeGenerationWithStepImpl(
        cellState: HashLifeCellState,
        @IntRange(from = 0) step: Int,
    ): HashLifeCellState {
        val initialStepState = HashLifeStepState(
            offsetX = cellState.offset.x,
            offsetY = cellState.offset.y,
            macroCell = cellState.macroCell,
        )
        val result = f_Algorithm_computeGenerationStep(
            step = step.toUInt(),
            st = initialStepState,
            computedGenerations = computedGenerations.toULong(),
            macroKeep = generationsToCacheInMacroCellMaps.toUInt(),
            leafKeep = generationsToCacheInLeafNodeMap.toUInt(),
            stepOneGen = { curr ->
                tracer.trace(
                    category = "LeanHashLifeAlgorithm",
                    name = "computeNextGeneration",
                ) {
                    val next = f_Algorithm_stepHashLifeStateWith(
                        st = curr,
                        stepPrepared = ::stepPrepared,
                    )
                    computedGenerations++
                    next
                }
            },
        )
        val finalStepState = result.finalState
        val oldestGenerationToKeepInMacroCellMaps = result.thresholds.oldestMacroToKeep.toLong()
        canonicalCellNodeMap.prune(oldestGenerationToKeepInMacroCellMaps)
        canonicalLevel4NodeMap.prune(oldestGenerationToKeepInMacroCellMaps)
        cellNodeMap.prune(oldestGenerationToKeepInMacroCellMaps)
        level4NodeMap.prune(oldestGenerationToKeepInMacroCellMaps)
        val oldestGenerationToKeepInLeafNodeMap = result.thresholds.oldestLeafToKeep.toLong()
        leafNodeMap.prune(oldestGenerationToKeepInLeafNodeMap)

        return HashLifeCellState(
            offset = IntOffset(finalStepState.offsetX, finalStepState.offsetY),
            macroCell = finalStepState.macroCell,
        )
    }
}
