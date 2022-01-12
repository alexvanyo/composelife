package com.alexvanyo.composelife.model

import androidx.compose.runtime.Stable
import androidx.compose.ui.unit.IntOffset
import com.alexvanyo.composelife.util.toIntOffset

/**
 * The cell state for a single generation.
 */
@Stable
abstract class CellState {
    /**
     * The set of all cells alive at this generation.
     */
    abstract val aliveCells: Set<IntOffset>

    override fun equals(other: Any?): Boolean =
        if (other !is CellState) {
            false
        } else {
            aliveCells.size == other.aliveCells.size &&
                aliveCells.containsAll(other.aliveCells)
        }

    override fun hashCode(): Int = aliveCells.toSet().hashCode()
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

/**
 * A simple implementation of [CellState] backed by a normal [Set].
 */
private class CellStateImpl(
    override val aliveCells: Set<IntOffset>
) : CellState() {
    override fun toString(): String = "CellStateImpl(${aliveCells.toSet()})"
}
