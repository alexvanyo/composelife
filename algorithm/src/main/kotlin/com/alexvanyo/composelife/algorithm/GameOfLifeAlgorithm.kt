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
        @IntRange(from = 0) step: Int
    ): CellState

    fun computeGenerationsWithStep(
        originalCellState: CellState,
        @IntRange(from = 0) step: Int
    ): Flow<CellState> = flow {
        var cellState = originalCellState
        while (currentCoroutineContext().isActive) {
            cellState = computeGenerationWithStep(
                cellState = cellState,
                step = step
            )
            emit(cellState)
        }
    }
}

/**
 * A helper function to compute one generation.
 */
suspend fun GameOfLifeAlgorithm.computeNextGeneration(
    cellState: CellState
): CellState = computeGenerationWithStep(cellState = cellState, step = 1)
