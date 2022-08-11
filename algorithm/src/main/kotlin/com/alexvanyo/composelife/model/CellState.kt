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

import androidx.compose.runtime.Stable
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
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
    cellStateSerializer: CellStateSerializer = PlaintextCellStateSerializer(),
    throwOnWarnings: Boolean = true,
): CellState {
    val deserializationResult = trimMargin()
        .split("\n")
        .asSequence()
        .run(cellStateSerializer::deserializeToCellState)

    return when (deserializationResult) {
        is CellStateSerializer.DeserializationResult.Successful -> {
            check(deserializationResult.warnings.isEmpty() || !throwOnWarnings) {
                "Warnings when parsing cell state!"
            }
            deserializationResult.cellState.offsetBy(topLeftOffset)
        }
        is CellStateSerializer.DeserializationResult.Unsuccessful ->
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
