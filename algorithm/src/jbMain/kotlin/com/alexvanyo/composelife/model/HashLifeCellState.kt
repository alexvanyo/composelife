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
import com.alexvanyo.composelife.model.MacroCell.LeafNode
import com.alexvanyo.composelife.model.MacroCell.Level4Node
import kotlin.math.ceil
import kotlin.math.log2

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

    val minimumLevel = ceil(
        maxOf(
            log2((maxX - minX).toDouble()),
            log2((maxY - minY).toDouble()),
        ),
    ).toInt().coerceAtLeast(4)

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

@Suppress("LongMethod")
internal fun HashLifeCellState.expandCentered(): HashLifeCellState {
    val node = macroCell

    val sameLevelEmptyCell = createEmptyMacroCell(node.level)

    val nwSe: MacroCell
    val neSw: MacroCell
    val swNe: MacroCell
    val seNw: MacroCell

    when (node) {
        is Level4Node -> {
            nwSe = Level4Node(
                nw = 0L,
                ne = 0L,
                sw = 0L,
                se = node.nw,
            )
            neSw = Level4Node(
                nw = 0L,
                ne = 0L,
                sw = node.ne,
                se = 0L,
            )
            swNe = Level4Node(
                nw = 0L,
                ne = node.sw,
                sw = 0L,
                se = 0L,
            )
            seNw = Level4Node(
                nw = node.se,
                ne = 0L,
                sw = 0L,
                se = 0L,
            )
        }
        is CellNode -> {
            val smallerLevelEmptyCell = createEmptyMacroCell(node.level - 1)

            nwSe = CellNode(
                nw = smallerLevelEmptyCell,
                ne = smallerLevelEmptyCell,
                sw = smallerLevelEmptyCell,
                se = node.nw,
            )
            neSw = CellNode(
                nw = smallerLevelEmptyCell,
                ne = smallerLevelEmptyCell,
                sw = node.ne,
                se = smallerLevelEmptyCell,
            )
            swNe = CellNode(
                nw = smallerLevelEmptyCell,
                ne = node.sw,
                sw = smallerLevelEmptyCell,
                se = smallerLevelEmptyCell,
            )
            seNw = CellNode(
                nw = node.se,
                ne = smallerLevelEmptyCell,
                sw = smallerLevelEmptyCell,
                se = smallerLevelEmptyCell,
            )
        }
    }

    val cell = CellNode(
        nw = CellNode(
            nw = sameLevelEmptyCell,
            ne = sameLevelEmptyCell,
            sw = sameLevelEmptyCell,
            se = nwSe,
        ),
        ne = CellNode(
            nw = sameLevelEmptyCell,
            ne = sameLevelEmptyCell,
            sw = neSw,
            se = sameLevelEmptyCell,
        ),
        sw = CellNode(
            nw = sameLevelEmptyCell,
            ne = swNe,
            sw = sameLevelEmptyCell,
            se = sameLevelEmptyCell,
        ),
        se = CellNode(
            nw = seNw,
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

internal class HashLifeCellState(
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
                CellWindow(
                    IntRect(
                        IntOffset.Zero,
                        IntSize(1 shl macroCell.level, 1 shl macroCell.level),
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

    override fun getAliveCellsInWindow(cellWindow: CellWindow): Iterable<IntOffset> =
        Iterable { macroCell.iterator(offset, cellWindow.translate(-offset)) }

    override fun toString(): String = "HashLifeCellState(${aliveCells.toSet()})"
}
