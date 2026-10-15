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

import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import androidx.compose.ui.unit.IntSize

/**
 * Converts the given [CellState] into the equivalent [HashLifeCellState].
 */
internal fun CellState.toHashLifeCellState(): HashLifeCellState {
    // Short-circuit if we already are
    if (this is HashLifeCellState) return this

    val xValues = aliveCells.map { it.x }
    val yValues = aliveCells.map { it.y }
    val minX = xValues.minOrNull() ?: 0
    val maxX = xValues.maxOrNull() ?: 0
    val minY = yValues.minOrNull() ?: 0
    val maxY = yValues.maxOrNull() ?: 0

    val span = maxOf(maxX + 1 - minX, maxY + 1 - minY)
    val minimumLevel = f_Algorithm_minimumMacroCellLevel(span.toUInt()).toInt()

    val offset = IntOffset(minX, minY)
    val macroCell =
        createMacroCell(
            cellState = this,
            offset = offset,
            level = minimumLevel,
        )

    return HashLifeCellState(
        offset = offset,
        macroCell = macroCell,
    )
}

internal fun HashLifeCellState.expandCentered(): HashLifeCellState {
    val delta = f_Algorithm_expandOffsetDeltaUInt(macroCell.level())
    return HashLifeCellState(
        offset = offset + IntOffset(delta, delta),
        macroCell = f_Algorithm_expandCentered(macroCell),
    )
}

internal class HashLifeCellState(val offset: IntOffset, val macroCell: MacroCell) : CellState() {
    override val aliveCells: Set<IntOffset> =
        object : Set<IntOffset> {
            override val size: Int = macroCell.size().toInt()

            override fun contains(element: IntOffset): Boolean = macroCell.contains(element - offset)

            override fun containsAll(elements: Collection<IntOffset>): Boolean =
                macroCell.containsAll(elements.map { it - offset })

            override fun isEmpty(): Boolean = size == 0

            override fun iterator(): Iterator<IntOffset> = macroCell.iterator(
                offset,
                CellWindow(
                    IntRect(
                        IntOffset.Zero,
                        IntSize(1 shl macroCell.level().toInt(), 1 shl macroCell.level().toInt()),
                    ),
                ),
            )
        }

    override fun offsetBy(offset: IntOffset) = HashLifeCellState(
        offset = this.offset + offset,
        macroCell = macroCell,
    )

    override fun withCell(offset: IntOffset, isAlive: Boolean): CellState {
        var hashLifeCellState = this

        var target: IntOffset

        while (
            run {
                target = offset - hashLifeCellState.offset
                val size = 1 shl hashLifeCellState.macroCell.level().toInt()
                target.x !in 0 until size || target.y !in 0 until size
            }
        ) {
            hashLifeCellState = hashLifeCellState.expandCentered()
        }

        return HashLifeCellState(
            offset = hashLifeCellState.offset,
            macroCell = hashLifeCellState.macroCell.withCell(target, isAlive),
        )
    }

    override fun getAliveCellsInWindow(cellWindow: CellWindow): Iterable<IntOffset> =
        Iterable { macroCell.iterator(offset, cellWindow.translate(-offset)) }

    override fun toString(): String = "HashLifeCellState(${aliveCells.toSet()})"
}
