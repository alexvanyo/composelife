package com.alexvanyo.composelife.data.model

import androidx.compose.runtime.Stable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.compose.ui.unit.IntOffset
import com.alexvanyo.composelife.util.toIntOffset

@Stable
interface CellState {
    val aliveCells: Set<IntOffset>
}

private data class CellStateImpl(override val aliveCells: Set<IntOffset>) : CellState {
    override fun equals(other: Any?): Boolean =
        if (other !is CellState) {
            false
        } else {
            aliveCells == other.aliveCells
        }

    override fun hashCode(): Int = aliveCells.hashCode()
}

fun CellState(aliveCells: Set<IntOffset>): CellState = CellStateImpl(aliveCells)

fun CellState.union(other: CellState) = CellState(aliveCells.union(other.aliveCells))

fun CellState.offsetBy(offset: IntOffset) = CellState(aliveCells.map { it + offset }.toSet())

fun emptyCellState(): CellState = CellState(emptySet())

fun Set<Pair<Int, Int>>.toCellState(): CellState = CellState(map(Pair<Int, Int>::toIntOffset).toSet())

fun String.toCellState(topLeftOffset: IntOffset = IntOffset.Zero): CellState =
    trimMargin()
        .split("\n")
        .flatMapIndexed { rowIndex, line ->
            line
                .withIndex()
                .filter { (_, c) -> c != ' ' }
                .map { (columnIndex, _) -> IntOffset(columnIndex, rowIndex) + topLeftOffset }
        }
        .toSet()
        .let(::CellState)

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
        CellState(cellState.aliveCells + cellCoordinate)
    } else {
        CellState(cellState.aliveCells - cellCoordinate)
    }
}
