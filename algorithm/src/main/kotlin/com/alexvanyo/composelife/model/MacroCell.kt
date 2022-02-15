package com.alexvanyo.composelife.model

import androidx.annotation.IntRange
import androidx.compose.ui.unit.IntOffset
import com.alexvanyo.composelife.model.MacroCell.Cell
import com.alexvanyo.composelife.model.MacroCell.Cell.AliveCell
import com.alexvanyo.composelife.model.MacroCell.Cell.DeadCell
import com.alexvanyo.composelife.model.MacroCell.CellNode

/**
 * A quad tree representation of the state of cells.
 *
 * A [MacroCell] is either a leaf [Cell], or a [CellNode] with 4 subnodes.
 */
sealed interface MacroCell {

    /**
     * The tree level of this cell. A cell at level `x` represents `4^x` cells.
     */
    val level: Int

    /**
     * The number of alive cells represented by this [MacroCell].
     *
     * This number is in the range of `0` and `4^x` (inclusive)
     */
    val size: Int

    /**
     * A leaf [MacroCell], which is either an [AliveCell] or a [DeadCell].
     */
    sealed interface Cell : MacroCell {

        override val level get() = 0

        val isAlive: Boolean

        object AliveCell : Cell {
            override val isAlive = true

            override val size: Int = 1
        }

        object DeadCell : Cell {
            override val isAlive = false

            override val size: Int = 0
        }
    }

    /**
     * A non-leaf [MacroCell], which contains 4 subnode [MacroCell]s.
     */
    data class CellNode(
        val nw: MacroCell,
        val ne: MacroCell,
        val sw: MacroCell,
        val se: MacroCell,
    ) : MacroCell {
        init {
            require(nw.level == ne.level)
            require(ne.level == sw.level)
            require(sw.level == se.level)
        }

        override val level = nw.level + 1

        override val size = nw.size + ne.size + sw.size + se.size

        /**
         * Memoize the hashcode.
         *
         * TODO: Is there a better hashcode function?
         */
        private val hashCode = run {
            var hash = level
            hash *= 31
            hash += nw.hashCode()
            hash *= 31
            hash += ne.hashCode()
            hash *= 31
            hash += sw.hashCode()
            hash *= 31
            hash += se.hashCode()
            hash
        }

        override fun hashCode(): Int = hashCode
    }
}

/**
 * Returns this [MacroCell] with the modification of setting the cell at the given [target] offset to [isAlive],
 * where [IntOffset.Zero] refers to the upper left cell of the [MacroCell].
 *
 * This function will return a [MacroCell] with the same level. Therefore, [target] must refer to a valid cell
 * contained by this [MacroCell].
 */
fun MacroCell.withCell(target: IntOffset, isAlive: Boolean): MacroCell {
    require(target.x in 0 until (1 shl level) && target.y in 0 until (1 shl level))
    return when (this) {
        AliveCell, DeadCell -> {
            require(target == IntOffset.Zero)
            if (isAlive) {
                AliveCell
            } else {
                DeadCell
            }
        }
        is CellNode -> {
            val offsetDiff = 1 shl (level - 1)
            val isNorth = target.y < offsetDiff
            val isWest = target.x < offsetDiff
            if (isNorth) {
                if (isWest) {
                    CellNode(
                        nw = nw.withCell(target, isAlive),
                        ne = ne,
                        sw = sw,
                        se = se
                    )
                } else {
                    CellNode(
                        nw = nw,
                        ne = ne.withCell(target + IntOffset(-offsetDiff, 0), isAlive),
                        sw = sw,
                        se = se
                    )
                }
            } else {
                if (isWest) {
                    CellNode(
                        nw = nw,
                        ne = ne,
                        sw = sw.withCell(target + IntOffset(0, -offsetDiff), isAlive),
                        se = se
                    )
                } else {
                    CellNode(
                        nw = nw,
                        ne = ne,
                        sw = sw,
                        se = se.withCell(target + IntOffset(-offsetDiff, -offsetDiff), isAlive)
                    )
                }
            }
        }
    }
}

/**
 * Creates a [MacroCell] with the given [level] as a window looking into [CellState] at [offset].
 */
fun createMacroCell(cellState: CellState, offset: IntOffset, level: Int): MacroCell =
    if (level == 0) {
        if (offset in cellState.aliveCells) {
            AliveCell
        } else {
            DeadCell
        }
    } else {
        val offsetDiff = 1 shl (level - 1)
        CellNode(
            createMacroCell(cellState, offset, level - 1),
            createMacroCell(cellState, offset + IntOffset(offsetDiff, 0), level - 1),
            createMacroCell(cellState, offset + IntOffset(0, offsetDiff), level - 1),
            createMacroCell(cellState, offset + IntOffset(offsetDiff, offsetDiff), level - 1),
        )
    }

/**
 * Creates an empty [MacroCell] with the given [level].
 *
 * The returned [MacroCell] has [MacroCell.size] `0` (in other words, it is entirely dead).
 */
fun createEmptyMacroCell(@IntRange(from = 0) level: Int): MacroCell {
    require(level >= 0)
    return if (level == 0) {
        DeadCell
    } else {
        val smallerEmptyMacroCell = createEmptyMacroCell(level - 1)
        CellNode(
            smallerEmptyMacroCell,
            smallerEmptyMacroCell,
            smallerEmptyMacroCell,
            smallerEmptyMacroCell
        )
    }
}

/**
 * Returns an [Iterator] of [IntOffset] for every alive cell represented by this [MacroCell],
 * with the given upper left corner [offset].
 */
fun MacroCell.iterator(
    offset: IntOffset,
): Iterator<IntOffset> = iterator {
    if (size > 0) {
        when (this@iterator) {
            AliveCell -> yield(offset)
            DeadCell -> throw AssertionError("Dead cell must have a size equal to 0!")
            is CellNode -> {
                val offsetDiff = 1 shl (level - 1)
                yieldAll(nw.iterator(offset))
                yieldAll(ne.iterator(offset + IntOffset(offsetDiff, 0)))
                yieldAll(sw.iterator(offset + IntOffset(0, offsetDiff)))
                yieldAll(se.iterator(offset + IntOffset(offsetDiff, offsetDiff)))
            }
        }
    }
}

/**
 * Returns true if the given [MacroCell] contains an alive cell with the given [target] offset, where
 * [IntOffset.Zero] refers to the upper-left corner of the [MacroCell].
 *
 * This runs in O(level) time.
 */
@Suppress("NestedBlockDepth")
tailrec fun MacroCell.contains(target: IntOffset): Boolean =
    if (target.x !in 0 until (1 shl level) || target.y !in 0 until (1 shl level)) {
        false
    } else {
        when (this) {
            is Cell -> isAlive
            is CellNode -> {
                if (size == 0) {
                    false
                } else {
                    val offsetDiff = 1 shl (level - 1)
                    val isNorth = target.y < offsetDiff
                    val isWest = target.x < offsetDiff
                    if (isNorth) {
                        if (isWest) {
                            nw.contains(target)
                        } else {
                            ne.contains(target + IntOffset(-offsetDiff, 0))
                        }
                    } else {
                        if (isWest) {
                            sw.contains(target + IntOffset(0, -offsetDiff))
                        } else {
                            se.contains(target + IntOffset(-offsetDiff, -offsetDiff))
                        }
                    }
                }
            }
        }
    }
