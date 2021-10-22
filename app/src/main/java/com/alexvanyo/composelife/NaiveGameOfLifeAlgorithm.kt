package com.alexvanyo.composelife

import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect

object NaiveGameOfLifeAlgorithm : GameOfLifeAlgorithm {
    override fun computeNextGeneration(cellState: CellState): CellState {
        val xCoordinates = cellState.map { it.x }
        val yCoordinates = cellState.map { it.y }
        val minX = xCoordinates.minOrNull() ?: 0
        val maxX = xCoordinates.maxOrNull() ?: 0
        val minY = yCoordinates.minOrNull() ?: 0
        val maxY = yCoordinates.maxOrNull() ?: 0

        val outputState = mutableSetOf<IntOffset>()

        val cellUniverse = IntRect(
            IntOffset(
                minX - 1,
                minY - 1,
            ),
            IntOffset(
                maxX + 1,
                maxY + 1
            )
        )

        cellUniverse.containedPoints().forEach { cell ->
            val neighborCount = cellState.intersect(cell.getNeighbors()).count()

            if (neighborCount == 3 || (neighborCount == 2 && cell in cellState)) {
                outputState.add(cell)
            }
        }

        return outputState
    }
}
