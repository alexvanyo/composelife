package com.alexvanyo.composelife

import androidx.compose.runtime.Stable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue

@Stable
interface GameOfLifeState {
    val cellState: Set<Pair<Int, Int>>
}

class ImmutableGameOfLifeState(
    override val cellState: Set<Pair<Int, Int>>
) : GameOfLifeState

interface MutableGameOfLifeState : GameOfLifeState {
    override var cellState: Set<Pair<Int, Int>>
}

class MutableGameOfLifeStateImpl(
    cellState: Set<Pair<Int, Int>>
) : MutableGameOfLifeState {
    override var cellState by mutableStateOf(cellState)
}

fun MutableGameOfLifeState.setIndividualCellState(cellCoordinate: Pair<Int, Int>, isAlive: Boolean) {
    cellState = if (isAlive) {
        cellState + cellCoordinate
    } else {
        cellState - cellCoordinate
    }
}
