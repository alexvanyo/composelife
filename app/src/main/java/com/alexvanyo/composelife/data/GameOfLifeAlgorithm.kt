package com.alexvanyo.composelife.data

import com.alexvanyo.composelife.data.model.CellState

interface GameOfLifeAlgorithm {

    fun computeNextGeneration(
        cellState: CellState,
    ): CellState
}
