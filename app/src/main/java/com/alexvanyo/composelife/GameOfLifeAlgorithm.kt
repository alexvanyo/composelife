package com.alexvanyo.composelife

interface GameOfLifeAlgorithm {

    fun computeNextGeneration(
        cellState: CellState,
    ): CellState
}
