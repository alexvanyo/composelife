package com.alexvanyo.composelife.data.model

import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.compose.ui.unit.IntOffset
import com.alexvanyo.composelife.util.toIntOffset

typealias CellState = Set<IntOffset>

fun emptyCellState(): CellState = emptySet()

fun Set<Pair<Int, Int>>.toCellState(): CellState = map(Pair<Int, Int>::toIntOffset).toSet()

interface GameOfLifeState {
    val cellState: CellState
}

private class ImmutableGameOfLifeState(
    override val cellState: CellState
) : GameOfLifeState

fun GameOfLifeState(cellState: CellState): GameOfLifeState = ImmutableGameOfLifeState(cellState)

interface MutableGameOfLifeState : GameOfLifeState {
    override var cellState: CellState
}

fun MutableGameOfLifeState(cellState: CellState): MutableGameOfLifeState = MutableGameOfLifeStateImpl(cellState)

private class MutableGameOfLifeStateImpl(
    cellState: CellState
) : MutableGameOfLifeState {
    override var cellState by mutableStateOf(cellState)
}

fun MutableGameOfLifeState.setIndividualCellState(cellCoordinate: IntOffset, isAlive: Boolean) {
    cellState = if (isAlive) {
        cellState + cellCoordinate
    } else {
        cellState - cellCoordinate
    }
}
