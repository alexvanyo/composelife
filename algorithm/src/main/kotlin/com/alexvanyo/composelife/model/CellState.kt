/*
 * Copyright 2022 The Android Open Source Project
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

package com.alexvanyo.composelife.model

import androidx.compose.runtime.Immutable
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import com.alexvanyo.composelife.util.containedPoints
import com.alexvanyo.composelife.util.toIntOffset
import kotlin.math.ceil

/**
 * The cell state for a single generation.
 */
@Immutable
abstract class CellState {
    /**
     * The set of all cells alive at this generation.
     */
    abstract val aliveCells: Set<IntOffset>

    /**
     * Returns a new cell state, where a cell is alive in the new cell state if it is alive in
     * this cell state, or in the [other] cell state (OR).
     *
     * This is overridable by subclasses in case the operation can be done more efficiently in a
     * particular implementation.
     */
    open fun union(other: CellState) = CellState(aliveCells.union(other.aliveCells))

    /**
     * Returns a new cell state with offset by the given [offset].
     *
     * This is overridable by subclasses in case the operation can be done more efficiently in a
     * particular implementation.
     */
    open fun offsetBy(offset: IntOffset) = CellState(aliveCells.map { it + offset }.toSet())

    /**
     * Returns a new cell state where the cell at the given [offset] is set to be alive or dead as
     * specified by [isAlive].
     *
     * This is overridable by subclasses in case the operation can be done more efficiently in a
     * particular implementation.
     */
    open fun withCell(offset: IntOffset, isAlive: Boolean): CellState =
        if (isAlive) {
            CellState(aliveCells + offset)
        } else {
            CellState(aliveCells - offset)
        }

    /**
     * Returns the list of alive cells that are contained within the given [cellWindow].
     *
     * This is overridable by subclasses in case the operation can be done more efficiently in a
     * particular implementation.
     */
    open fun getAliveCellsInWindow(cellWindow: IntRect): Iterable<IntOffset> =
        cellWindow.containedPoints().filter { it in aliveCells }

    open fun getShortPackedAliveCellsInWindow(cellWindow: IntRect): Pair<IntOffset, Iterable<Pair<IntOffset, UShort>>> {
        val minX = cellWindow.left
        val maxX = cellWindow.right
        val minY = cellWindow.top
        val maxY = cellWindow.bottom

        val shortPackedAliveCells = buildList {
            (0 until ceil(maxX + 1 - minX / 4f).toInt()).forEach { metaX ->
                (0 until ceil(maxY + 1 - minY / 4f).toInt()).forEach { metaY ->
                    val value = (if (cellWindow.topLeft + IntOffset(metaX, metaY) in aliveCells) 1 shl 0 else 0) or
                        (if (cellWindow.topLeft + IntOffset(metaX + 1, metaY) in aliveCells) 1 shl 1 else 0) or
                        (if (cellWindow.topLeft + IntOffset(metaX, metaY + 1) in aliveCells) 1 shl 2 else 0) or
                        (if (cellWindow.topLeft + IntOffset(metaX + 1, metaY + 1) in aliveCells) 1 shl 3 else 0) or
                        (if (cellWindow.topLeft + IntOffset(metaX + 2, metaY) in aliveCells) 1 shl 4 else 0) or
                        (if (cellWindow.topLeft + IntOffset(metaX + 3, metaY) in aliveCells) 1 shl 5 else 0) or
                        (if (cellWindow.topLeft + IntOffset(metaX + 2, metaY + 1) in aliveCells) 1 shl 6 else 0) or
                        (if (cellWindow.topLeft + IntOffset(metaX + 3, metaY + 1) in aliveCells) 1 shl 7 else 0) or
                        (if (cellWindow.topLeft + IntOffset(metaX, metaY + 2) in aliveCells) 1 shl 8 else 0) or
                        (if (cellWindow.topLeft + IntOffset(metaX + 1, metaY + 2) in aliveCells) 1 shl 9 else 0) or
                        (if (cellWindow.topLeft + IntOffset(metaX, metaY + 3) in aliveCells) 1 shl 10 else 0) or
                        (if (cellWindow.topLeft + IntOffset(metaX + 1, metaY + 3) in aliveCells) 1 shl 11 else 0) or
                        (if (cellWindow.topLeft + IntOffset(metaX + 2, metaY + 2) in aliveCells) 1 shl 12 else 0) or
                        (if (cellWindow.topLeft + IntOffset(metaX + 3,  + 2) in aliveCells) 1 shl 13 else 0) or
                        (if (cellWindow.topLeft + IntOffset(metaX + 2, metaY + 3) in aliveCells) 1 shl 14 else 0) or
                        (if (cellWindow.topLeft + IntOffset(metaX + 3, metaY + 3) in aliveCells) 1 shl 15 else 0)

                    check(value <= UShort.MAX_VALUE.toInt())
                    if (value != 0) {
                        add(IntOffset(metaX, metaY) to value.toUShort())
                    }
                }
            }
        }

        return IntOffset.Zero to shortPackedAliveCells
    }

    /**
     * Returns the [IntRect] describing the minimal bounding box required to enclose all alive cells
     * in this cell state. If the cell state is empty, this will return [IntRect.Zero].
     *
     * This is overridable by subclasses in case the operation can be done more efficiently in a
     * particular implementation.
     */
    open val boundingBox: IntRect get() =
        if (aliveCells.isEmpty()) {
            IntRect.Zero
        } else {
            IntRect(
                left = aliveCells.minOf { it.x },
                top = aliveCells.minOf { it.y },
                right = aliveCells.maxOf { it.x },
                bottom = aliveCells.maxOf { it.y },
            )
        }

    override fun equals(other: Any?): Boolean =
        if (other !is CellState) {
            false
        } else {
            aliveCells.size == other.aliveCells.size &&
                aliveCells.containsAll(other.aliveCells)
        }

    override fun hashCode(): Int = aliveCells.toSet().hashCode()
}

/**
 * Returns `true` if this [CellState] and the [other] [CellState] are equivalent with the possible exception of being
 * offset differently (in other words, different only by translation).
 *
 * This does not attempt to check equivalence against rotation or reflection.
 */
fun CellState.equalsModuloOffset(other: CellState): Boolean =
    if (aliveCells.size != other.aliveCells.size) {
        false
    } else if (aliveCells.isEmpty()) {
        true
    } else {
        val topLeftOffset = IntOffset(aliveCells.minOf(IntOffset::x), aliveCells.minOf(IntOffset::y))
        val otherTopLeftOffset = IntOffset(other.aliveCells.minOf(IntOffset::x), other.aliveCells.minOf(IntOffset::y))
        offsetBy(otherTopLeftOffset - topLeftOffset) == other
    }

fun CellState(aliveCells: Set<IntOffset>): CellState = CellStateImpl(aliveCells)

fun emptyCellState(): CellState = CellState(emptySet())

fun Set<Pair<Int, Int>>.toCellState(): CellState = CellState(map(Pair<Int, Int>::toIntOffset).toSet())

fun String.toCellState(
    topLeftOffset: IntOffset = IntOffset.Zero,
    fixedFormatCellStateSerializer: FixedFormatCellStateSerializer = PlaintextCellStateSerializer,
    throwOnWarnings: Boolean = true,
): CellState {
    val deserializationResult = trimMargin()
        .split("\n")
        .asSequence()
        .run(fixedFormatCellStateSerializer::deserializeToCellState)

    return when (deserializationResult) {
        is DeserializationResult.Successful -> {
            check(deserializationResult.warnings.isEmpty() || !throwOnWarnings) {
                "Warnings when parsing cell state!"
            }
            deserializationResult.cellState.offsetBy(topLeftOffset)
        }
        is DeserializationResult.Unsuccessful ->
            error("Could not parse cell state!")
    }
}

/**
 * A simple implementation of [CellState] backed by a normal [Set].
 */
private class CellStateImpl(
    override val aliveCells: Set<IntOffset>,
) : CellState() {
    override fun toString(): String = "CellStateImpl(${aliveCells.toSet()})"
}
