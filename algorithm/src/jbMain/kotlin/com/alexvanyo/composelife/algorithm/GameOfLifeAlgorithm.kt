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
import com.alexvanyo.composelife.model.CellState
import kotlinx.coroutines.currentCoroutineContext
import kotlinx.coroutines.flow.Flow
import kotlinx.coroutines.flow.flow
import kotlinx.coroutines.isActive

/**
 * An implementation of the Game of Life algorithm.
 */
interface GameOfLifeAlgorithm {

    /**
     * Computes the [CellState] corresponding to the evolution of the current [CellState] a total of [step] generations.
     * A [step] of `0` indicates that no generations should be be calculated, and the given [CellState] should be equal
     * to the returned [CellState].
     */
    suspend fun computeGenerationWithStep(
        cellState: CellState,
        @IntRange(from = 0) step: Int,
    ): CellState

    fun computeGenerationsWithStep(
        originalCellState: CellState,
        @IntRange(from = 0) step: Int,
    ): Flow<CellState> = flow {
        var cellState = originalCellState
        while (currentCoroutineContext().isActive) {
            cellState = computeGenerationWithStep(
                cellState = cellState,
                step = step,
            )
            emit(cellState)
        }
    }
}

/**
 * A helper function to compute one generation.
 */
suspend fun GameOfLifeAlgorithm.computeNextGeneration(
    cellState: CellState,
): CellState = computeGenerationWithStep(cellState = cellState, step = 1)
