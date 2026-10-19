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

@file:OptIn(ExperimentalUnsignedTypes::class)

package com.alexvanyo.composelife.algorithm

import androidx.annotation.IntRange
import androidx.compose.ui.unit.IntOffset
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.model.FlatHashLifeCellState
import com.alexvanyo.composelife.model.HashLifeCellState
import com.alexvanyo.composelife.model.UNCOMPUTED_ID
import com.alexvanyo.composelife.model.buildQuadtreeBottomUp
import com.alexvanyo.composelife.model.createFlatArena
import com.alexvanyo.composelife.model.internMacroCellDag
import com.alexvanyo.composelife.tracing.Tracer
import com.alexvanyo.composelife.tracing.traceCoroutine
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.Inject
import dev.zacsweers.metro.SingleIn
import kotlinx.coroutines.currentCoroutineContext
import kotlinx.coroutines.ensureActive
import kotlinx.coroutines.sync.Mutex
import kotlinx.coroutines.sync.withLock
import kotlinx.coroutines.withContext

/**
 * A [GameOfLifeAlgorithm] implementation backed by a Lean 4 flat-memory arena ([FlatHashLifeArena])
 * with zero heap allocations in the recursive HashLife step loop, mark-compact generational memo retention,
 * and append-only zero-copy UI snapshots.
 *
 * This implementation is differential-tested against [HashLifeAlgorithm].
 */
@SingleIn(AppScope::class)
@Inject
class FlatLeanHashLifeAlgorithm(
    private val dispatchers: ComposeLifeDispatchers,
    private val tracer: Tracer,
    private val initialCapacityPow2: Int = 14,
    private val maxCapacityPow2: Int = 18,
) : GameOfLifeAlgorithm {

    private val mutex = Mutex()

    private var currentCapacityPow2: Int = initialCapacityPow2.coerceIn(6, maxCapacityPow2)
    private var mainArena: FlatHashLifeArena? = null

    private fun createArena(capacityPow2: Int): FlatHashLifeArena = createFlatArena(capacityPow2, maxCapacityPow2)

    private fun getOrCreateMainArena(): FlatHashLifeArena {
        var arena = mainArena
        if (arena == null) {
            arena = createArena(currentCapacityPow2)
            mainArena = arena
        }
        return arena
    }

    /**
     * Performs a mark-compact pass from [activeRootId] in [oldArena] into a freshly allocated
     * arena (growing capacity up to [maxCapacityPow2] when needed), preserving all reachable
     * nodes and their memoized step results while leaving [oldArena]'s arrays untouched for
     * any existing [FlatHashLifeCellState] snapshots.
     */
    private fun compactOrGrowArena(
        oldArena: FlatHashLifeArena,
        activeRootId: UInt?,
        forceGrow: Boolean,
    ): Pair<FlatHashLifeArena, UInt?> {
        if (forceGrow && currentCapacityPow2 < maxCapacityPow2) {
            currentCapacityPow2++
        }
        var result: Pair<FlatHashLifeArena, UInt?>? = null
        while (result == null) {
            val newArena = createArena(currentCapacityPow2)
            if (activeRootId == null || oldArena.overflow != 0u.toUByte()) {
                mainArena = newArena
                result = newArena to null
            } else {
                val res = newArena.compactRootFrom(oldArena, activeRootId)
                val newRootId = res.first
                if (newArena.overflow == 0u.toUByte() && newRootId != UNCOMPUTED_ID) {
                    if (currentCapacityPow2 < maxCapacityPow2 && newArena.isOver60Percent()) {
                        currentCapacityPow2++
                    } else {
                        mainArena = newArena
                        result = newArena to newRootId
                    }
                } else if (currentCapacityPow2 < maxCapacityPow2) {
                    currentCapacityPow2++
                } else {
                    mainArena = newArena
                    result = newArena to if (newRootId == UNCOMPUTED_ID) null else newRootId
                }
            }
        }
        return result
    }

    private fun tryResolveGenericCellStateInArena(
        cellState: CellState,
        arena: FlatHashLifeArena,
    ): Pair<IntOffset, UInt>? = buildQuadtreeBottomUp(cellState, arena)

    private fun tryResolveInCurrentArena(cellState: CellState, arena: FlatHashLifeArena): Pair<IntOffset, UInt>? =
        when (cellState) {
            is FlatHashLifeCellState -> {
                if (!arena.canCopySubgraphFrom(cellState.arena)) {
                    tryResolveGenericCellStateInArena(cellState, arena)
                } else {
                    val rootId = arena.copySubgraphFrom(cellState.arena, cellState.rootNodeId, false)
                    if (rootId != UNCOMPUTED_ID) {
                        cellState.offset to rootId
                    } else {
                        null
                    }
                }
            }

            is HashLifeCellState -> internMacroCellDag(cellState, arena)

            else -> tryResolveGenericCellStateInArena(cellState, arena)
        }

    /**
     * Resolves any [CellState] into `(offset, rootNodeId)` at level >= 5 in the active arena,
     * growing/compacting the arena if capacity is exceeded.
     */
    private fun resolveCellStateInArena(cellState: CellState): Pair<IntOffset, UInt> {
        var arena = getOrCreateMainArena()
        if (cellState is FlatHashLifeCellState && cellState.arena === arena) {
            return cellState.offset to cellState.rootNodeId
        }
        var resolved = tryResolveInCurrentArena(cellState, arena)
        while (resolved == null) {
            if (currentCapacityPow2 >= maxCapacityPow2) {
                if (arena.cellCount > 0u || arena.l4Count > 0u || arena.overflow != 0u.toUByte()) {
                    arena = createArena(maxCapacityPow2)
                    mainArena = arena
                    currentCapacityPow2 = maxCapacityPow2
                    resolved = tryResolveInCurrentArena(cellState, arena)
                    if (resolved != null) {
                        break
                    }
                }
                throw FlatHashLifeArenaException(
                    "Failed to fit pattern into FlatHashLifeArena at maximum capacity ($maxCapacityPow2)",
                )
            }
            arena = compactOrGrowArena(arena, null, forceGrow = true).first
            resolved = tryResolveInCurrentArena(cellState, arena)
        }
        return checkNotNull(resolved)
    }

    @Suppress("TooGenericExceptionCaught")
    override suspend fun computeGenerationWithStep(cellState: CellState, @IntRange(from = 0) step: Int): CellState =
        tracer.traceCoroutine(
            category = "FlatLeanHashLifeAlgorithm",
            name = "computeGenerationWithStep",
        ) {
            withContext(dispatchers.Default) {
                mutex.withLock {
                    try {
                        var (currOffset, currRootId) = resolveCellStateInArena(cellState)
                        var arena = getOrCreateMainArena()

                        repeat(step) {
                            currentCoroutineContext().ensureActive()
                            if (arena.isNearCapacity()) {
                                val compacted = compactOrGrowArena(arena, currRootId, forceGrow = false)
                                arena = compacted.first
                                currRootId = compacted.second ?: throw compactionFailed()
                            }

                            var res = arena.stepOneGeneration(currOffset.x, currOffset.y, currRootId)

                            while (res.second.second == UNCOMPUTED_ID) {
                                if (arena.overflow == 0u.toUByte()) {
                                    // A step of a valid root only fails without the overflow flag when the next
                                    // generation does not fit in the 32-bit coordinate range of the flat engine.
                                    throw FlatHashLifeArenaException(
                                        "Next generation exceeds the coordinate range of FlatHashLifeArena",
                                    )
                                }
                                if (currentCapacityPow2 >= maxCapacityPow2) {
                                    throw FlatHashLifeArenaException(
                                        "FlatHashLifeArena exceeded maximum capacity ($maxCapacityPow2) " +
                                            "during generation step",
                                    )
                                }
                                arena.overflow = 0u
                                val compacted = compactOrGrowArena(arena, currRootId, forceGrow = true)
                                arena = compacted.first
                                currRootId = compacted.second ?: throw compactionFailed()
                                res = arena.stepOneGeneration(currOffset.x, currOffset.y, currRootId)
                            }

                            currOffset = IntOffset(res.first, res.second.first)
                            currRootId = res.second.second
                        }

                        FlatHashLifeCellState(currOffset, currRootId, arena)
                    } catch (t: Throwable) {
                        mainArena = null
                        currentCapacityPow2 = initialCapacityPow2
                        throw t
                    }
                }
            }
        }

    private fun compactionFailed(): FlatHashLifeArenaException = FlatHashLifeArenaException(
        "Failed to compact the active pattern into FlatHashLifeArena at maximum capacity ($maxCapacityPow2)",
    )
}
