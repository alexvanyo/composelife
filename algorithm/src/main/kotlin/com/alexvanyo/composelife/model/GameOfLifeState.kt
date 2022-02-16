package com.alexvanyo.composelife.model

import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.compose.ui.unit.IntOffset

interface GameOfLifeState {
    val cellState: CellState
}

private class ImmutableGameOfLifeState(
    override val cellState: CellState,
) : GameOfLifeState

fun GameOfLifeState(cellState: CellState): GameOfLifeState = ImmutableGameOfLifeState(cellState)

interface MutableGameOfLifeState : GameOfLifeState {
    override var cellState: CellState
}

fun MutableGameOfLifeState(cellState: CellState): MutableGameOfLifeState = MutableGameOfLifeStateImpl(cellState)

private class MutableGameOfLifeStateImpl(
    cellState: CellState,
) : MutableGameOfLifeState {
    override var cellState by mutableStateOf(cellState)
}

fun MutableGameOfLifeState.setCellState(cellCoordinate: IntOffset, isAlive: Boolean) {
    cellState = cellState.withCell(cellCoordinate, isAlive)
}
