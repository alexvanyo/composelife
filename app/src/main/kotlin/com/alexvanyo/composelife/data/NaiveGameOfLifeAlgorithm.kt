package com.alexvanyo.composelife.data

import androidx.annotation.IntRange
import androidx.compose.ui.unit.IntOffset
import com.alexvanyo.composelife.data.model.CellState
import com.alexvanyo.composelife.util.getNeighbors
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.withContext

/**
 * The basic, naive implementation of the [GameOfLifeAlgorithm].
 *
 * Each generation is computed in turn, and each of the possible cells that could be alive in the next generation
 * is checked individually.
 */
object NaiveGameOfLifeAlgorithm : GameOfLifeAlgorithm {
    override suspend fun computeGenerationWithStep(
        cellState: CellState,
        @IntRange(from = 0) step: Int
    ): CellState =
        withContext(Dispatchers.Default) {
            computeGenerationWithStepImpl(
                cellState = cellState,
                step = step
            )
        }

    private tailrec fun computeGenerationWithStepImpl(
        cellState: CellState,
        @IntRange(from = 0) step: Int
    ): CellState =
        if (step == 0) {
            cellState
        } else {
            computeGenerationWithStepImpl(
                cellState = computeNextGeneration(cellState),
                step = step - 1
            )
        }

    private fun computeNextGeneration(cellState: CellState): CellState =
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
