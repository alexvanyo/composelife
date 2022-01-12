package com.alexvanyo.composelife.algorithm

import androidx.annotation.IntRange
import androidx.compose.ui.unit.IntOffset
import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.util.getNeighbors
import kotlinx.coroutines.CoroutineDispatcher
import kotlinx.coroutines.withContext

/**
 * The basic, naive implementation of the [GameOfLifeAlgorithm].
 *
 * Each generation is computed in turn, and each of the possible cells that could be alive in the next generation
 * is checked individually.
 */
class NaiveGameOfLifeAlgorithm(
    private val backgroundDispatcher: CoroutineDispatcher
) : GameOfLifeAlgorithm {
    override suspend fun computeGenerationWithStep(
        cellState: CellState,
        @IntRange(from = 0) step: Int
    ): CellState =
        withContext(backgroundDispatcher) {
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
            .aliveCells
            // Get all neighbors of current living cells
            .flatMap(IntOffset::getNeighbors)
            .toSet()
            // Union those with all living cells, to get all cells that could be alive next round
            .union(cellState.aliveCells)
            // Filter to the living cells, based on the neighbor count from the previous generation
            .filter { cell ->
                val neighborCount = cellState.aliveCells.intersect(cell.getNeighbors()).count()
                neighborCount == 3 || (neighborCount == 2 && cell in cellState.aliveCells)
            }
            .toSet()
            .let(::CellState)
}
