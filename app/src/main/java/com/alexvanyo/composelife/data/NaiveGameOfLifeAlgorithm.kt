package com.alexvanyo.composelife.data

import androidx.compose.ui.unit.IntOffset
import com.alexvanyo.composelife.data.model.CellState
import com.alexvanyo.composelife.util.getNeighbors

object NaiveGameOfLifeAlgorithm : GameOfLifeAlgorithm {
    @OptIn(ExperimentalStdlibApi::class)
    override fun computeNextGeneration(cellState: CellState): CellState =
        cellState.flatMap(IntOffset::getNeighbors).toSet()
            .union(cellState)
            .filter { cell ->
                val neighborCount = cellState.intersect(cell.getNeighbors()).count()
                neighborCount == 3 || (neighborCount == 2 && cell in cellState)
            }
            .toSet()
}
