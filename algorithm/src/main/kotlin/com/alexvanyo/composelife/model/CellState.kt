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

    open fun union(other: CellState) = CellState(aliveCells.union(other.aliveCells))

    open fun offsetBy(offset: IntOffset) = CellState(aliveCells.map { it + offset }.toSet())

    open fun withCell(offset: IntOffset, isAlive: Boolean): CellState =
        if (isAlive) {
            CellState(aliveCells + offset)
        } else {
            CellState(aliveCells - offset)
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
            if (throwOnWarnings && deserializationResult.warnings.isNotEmpty()) {
                throw IllegalStateException("Warnings when parsing cell state!")
            }
            deserializationResult.cellState.offsetBy(topLeftOffset)
        }
        is CellStateSerializer.DeserializationResult.Unsuccessful ->
            throw IllegalStateException("Could not parse cell state!")
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
