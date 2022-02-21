package com.alexvanyo.composelife.model

import androidx.compose.ui.unit.IntOffset
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
            log2((maxY - minY).toDouble())
        )
    ).toInt().coerceAtLeast(3)

    val offset = IntOffset(minX, minY)
    val macroCell = createMacroCell(
        cellState = this,
        offset = offset,
        level = minimumLevel
    )

    return HashLifeCellState(
        offset = offset,
        macroCell = macroCell
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
                se = node.nw
            )
        ),
        ne = CellNode(
            nw = sameLevelEmptyCell,
            ne = sameLevelEmptyCell,
            sw = CellNode(
                nw = smallerLevelEmptyCell,
                ne = smallerLevelEmptyCell,
                sw = node.ne,
                se = smallerLevelEmptyCell
            ),
            se = sameLevelEmptyCell
        ),
        sw = CellNode(
            nw = sameLevelEmptyCell,
            ne = CellNode(
                nw = smallerLevelEmptyCell,
                ne = node.sw,
                sw = smallerLevelEmptyCell,
                se = smallerLevelEmptyCell
            ),
            sw = sameLevelEmptyCell,
            se = sameLevelEmptyCell
        ),
        se = CellNode(
            nw = CellNode(
                nw = node.se,
                ne = smallerLevelEmptyCell,
                sw = smallerLevelEmptyCell,
                se = smallerLevelEmptyCell
            ),
            ne = sameLevelEmptyCell,
            sw = sameLevelEmptyCell,
            se = sameLevelEmptyCell
        )
    )

    val offsetDiff = 3 * (1 shl (node.level - 1))

    return HashLifeCellState(
        offset = offset + IntOffset(-offsetDiff, -offsetDiff),
        macroCell = cell
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

        override fun iterator(): Iterator<IntOffset> = macroCell.iterator(offset)
    }

    override fun offsetBy(offset: IntOffset) = HashLifeCellState(
        offset = this.offset + offset,
        macroCell = macroCell
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
            macroCell = hashLifeCellState.macroCell.withCell(target, isAlive)
        )
    }

    override fun toString(): String = "HashLifeCellState(${aliveCells.toSet()})"
}
