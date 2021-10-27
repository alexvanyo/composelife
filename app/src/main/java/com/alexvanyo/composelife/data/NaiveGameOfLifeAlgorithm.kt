package com.alexvanyo.composelife.data

import androidx.compose.ui.unit.IntOffset
import com.alexvanyo.composelife.data.model.CellState
import com.alexvanyo.composelife.util.getNeighbors

object NaiveGameOfLifeAlgorithm : GameOfLifeAlgorithm {
    override fun computeNextGeneration(cellState: CellState): CellState =
        cellState
            // Get all neighbors of current living cells
            .flatMap(IntOffset::getNeighbors)
            .toSet()
            // Union those with all living cells, to get all cells that could be alive next round
            .union(cellState)
            // Filter to the living cells, based on the neighbor count from the previous generation
            .filter { cell ->
                val neighborCount = cellState.intersect(cell.getNeighbors()).count()
                neighborCount == 3 || (neighborCount == 2 && cell in cellState)
            }
            .toSet()
}
