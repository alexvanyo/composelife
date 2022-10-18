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
import com.alexvanyo.composelife.model.MacroCell.CellNode
import kotlin.math.ceil
import kotlin.math.log2

/**
 * Converts the given [CellState] into the equivalent [HashLifeCellState].
 */
fun CellState.toHashLifeCellState(): HashLifeCellState {
    // Short-circuit if we already are
    if (this is HashLifeCellState) return this

    val xValues = aliveCells.map { it.x }
    val yValues = aliveCells.map { it.y }
    val minX = xValues.minOrNull() ?: 0
    val maxX = xValues.maxOrNull() ?: 0
    val minY = yValues.minOrNull() ?: 0
    val maxY = yValues.maxOrNull() ?: 0

    val minimumLevel = ceil(
        maxOf(
            log2((maxX - minX).toDouble()),
            log2((maxY - minY).toDouble()),
        ),
    ).toInt().coerceAtLeast(3)

    val offset = IntOffset(minX, minY)
    val macroCell = createMacroCell(
        cellState = this,
        offset = offset,
        level = minimumLevel,
    )

    return HashLifeCellState(
        offset = offset,
        macroCell = macroCell,
    )
}

fun HashLifeCellState.expandCentered(): HashLifeCellState {
    val node = macroCell as CellNode

    val sameLevelEmptyCell = createEmptyMacroCell(node.level)
    val smallerLevelEmptyCell = createEmptyMacroCell(node.level - 1)

    val cell = CellNode(
        nw = CellNode(
            nw = sameLevelEmptyCell,
            ne = sameLevelEmptyCell,
            sw = sameLevelEmptyCell,
            se = CellNode(
                nw = smallerLevelEmptyCell,
                ne = smallerLevelEmptyCell,
                sw = smallerLevelEmptyCell,
                se = node.nw,
            ),
        ),
        ne = CellNode(
            nw = sameLevelEmptyCell,
            ne = sameLevelEmptyCell,
            sw = CellNode(
                nw = smallerLevelEmptyCell,
                ne = smallerLevelEmptyCell,
                sw = node.ne,
                se = smallerLevelEmptyCell,
            ),
            se = sameLevelEmptyCell,
        ),
        sw = CellNode(
            nw = sameLevelEmptyCell,
            ne = CellNode(
                nw = smallerLevelEmptyCell,
                ne = node.sw,
                sw = smallerLevelEmptyCell,
                se = smallerLevelEmptyCell,
            ),
            sw = sameLevelEmptyCell,
            se = sameLevelEmptyCell,
        ),
        se = CellNode(
            nw = CellNode(
                nw = node.se,
                ne = smallerLevelEmptyCell,
                sw = smallerLevelEmptyCell,
                se = smallerLevelEmptyCell,
            ),
            ne = sameLevelEmptyCell,
            sw = sameLevelEmptyCell,
            se = sameLevelEmptyCell,
        ),
    )

    val offsetDiff = 3 * (1 shl (node.level - 1))

    return HashLifeCellState(
        offset = offset + IntOffset(-offsetDiff, -offsetDiff),
        macroCell = cell,
    )
}

class HashLifeCellState(
    val offset: IntOffset,
    val macroCell: MacroCell,
) : CellState() {
    init {
        // Check the invariant for the macroCell
        check(macroCell.level >= 3)
    }

    override val aliveCells: Set<IntOffset> = object : Set<IntOffset> {
        override val size: Int = macroCell.size

        override fun contains(element: IntOffset): Boolean =
            macroCell.contains(element - offset)

        override fun containsAll(elements: Collection<IntOffset>): Boolean =
            macroCell.containsAll(elements.map { it - offset })

        override fun isEmpty(): Boolean = size == 0

        override fun iterator(): Iterator<IntOffset> =
            macroCell.iterator(
                offset,
                IntRect(IntOffset.Zero, IntSize((1 shl macroCell.level) - 1, (1 shl macroCell.level) - 1)),
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
                val size = 1 shl hashLifeCellState.macroCell.level
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

    override fun getAliveCellsInWindow(cellWindow: IntRect): Iterable<IntOffset> =
        Iterable { macroCell.iterator(offset, cellWindow.translate(-offset)) }

    override fun toString(): String = "HashLifeCellState(${aliveCells.toSet()})"
}
