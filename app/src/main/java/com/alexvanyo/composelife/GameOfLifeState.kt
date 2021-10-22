package com.alexvanyo.composelife

import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.compose.ui.unit.IntOffset

typealias CellState = Set<IntOffset>

interface GameOfLifeState {
    val cellState: CellState
}

private class ImmutableGameOfLifeState(
    override val cellState: CellState
) : GameOfLifeState

fun GameOfLifeState(cellState: CellState): GameOfLifeState = ImmutableGameOfLifeState(cellState)

@JvmName("GameOfLifeStatePairs")
fun GameOfLifeState(cellState: Set<Pair<Int, Int>>): GameOfLifeState =
    GameOfLifeState(cellState.map(Pair<Int, Int>::toIntOffset).toSet())

interface MutableGameOfLifeState : GameOfLifeState {
    override var cellState: CellState
}

fun MutableGameOfLifeState(cellState: CellState): MutableGameOfLifeState = MutableGameOfLifeStateImpl(cellState)

@JvmName("MutableGameOfLifeStatePairs")
fun MutableGameOfLifeState(cellState: Set<Pair<Int, Int>>): MutableGameOfLifeState =
    MutableGameOfLifeState(cellState.map(Pair<Int, Int>::toIntOffset).toSet())

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
