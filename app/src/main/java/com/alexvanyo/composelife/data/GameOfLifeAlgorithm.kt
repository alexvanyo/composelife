package com.alexvanyo.composelife.data

import androidx.annotation.IntRange
import com.alexvanyo.composelife.data.model.CellState

interface GameOfLifeAlgorithm {
    fun computeGenerationWithStep(
        cellState: CellState,
        @IntRange(from = 0) step: Int
    ): CellState
}

fun GameOfLifeAlgorithm.computeNextGeneration(
    cellState: CellState
): CellState = computeGenerationWithStep(cellState = cellState, step = 1)
