package com.alexvanyo.composelife.data

import androidx.annotation.IntRange
import com.alexvanyo.composelife.data.model.CellState

/**
 * An implementation of the Game of Life algorithm.
 */
interface GameOfLifeAlgorithm {

    /**
     * Computes the [CellState] corresponding to the evolution of the current [CellState] a total of [step] generations.
     * A [step] of `0` indicates that no generations should be be calculated, and the given [CellState] should be equal
     * to the returned [CellState].
     */
    fun computeGenerationWithStep(
        cellState: CellState,
        @IntRange(from = 0) step: Int
    ): CellState
}

/**
 * A helper function to compute one generation.
 */
fun GameOfLifeAlgorithm.computeNextGeneration(
    cellState: CellState
): CellState = computeGenerationWithStep(cellState = cellState, step = 1)
