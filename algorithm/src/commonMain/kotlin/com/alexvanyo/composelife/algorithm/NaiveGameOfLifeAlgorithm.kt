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
import com.alexvanyo.composelife.geometry.getNeighbors
import com.alexvanyo.composelife.model.CellState
import kotlinx.coroutines.withContext
import javax.inject.Inject

/**
 * The basic, naive implementation of the [GameOfLifeAlgorithm].
 *
 * Each generation is computed in turn, and each of the possible cells that could be alive in the next generation
 * is checked individually.
 */
class NaiveGameOfLifeAlgorithm @Inject constructor(
    private val dispatchers: ComposeLifeDispatchers,
) : GameOfLifeAlgorithm {
    override suspend fun computeGenerationWithStep(
        cellState: CellState,
        @IntRange(from = 0) step: Int,
    ): CellState =
        @Suppress("InjectDispatcher") // Dispatchers are injected via dispatchers
        withContext(dispatchers.Default) {
            computeGenerationWithStepImpl(
                cellState = cellState,
                step = step,
            )
        }

    private tailrec fun computeGenerationWithStepImpl(
        cellState: CellState,
        @IntRange(from = 0) step: Int,
    ): CellState =
        if (step == 0) {
            cellState
        } else {
            computeGenerationWithStepImpl(
                cellState = computeNextGeneration(cellState),
                step = step - 1,
            )
        }

    private fun computeNextGeneration(cellState: CellState): CellState =
        cellState
            .aliveCells
            // Get all neighbors of current living cells
            .flatMap(IntOffset::getNeighbors)
            .toSet()
            // Union those with all living cells, to get all cells that could be alive next round
            .union(cellState.aliveCells)
            // Filter to the living cells, based on the neighbor count from the previous generation
            .filter { cell ->
                val neighborCount = cellState.aliveCells.intersect(cell.getNeighbors()).count()
                neighborCount == 3 || (neighborCount == 2 && cell in cellState.aliveCells)
            }
            .toSet()
            .let(::CellState)
}
