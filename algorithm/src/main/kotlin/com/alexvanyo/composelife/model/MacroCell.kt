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

import androidx.annotation.IntRange
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
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

        val shortPackedValue get() = (if (isAlive) 1 else 0).toUShort()
    }

    /**
     * A non-leaf [MacroCell], which contains 4 subnode [MacroCell]s.
     */
    sealed class CellNode(
        open val nw: MacroCell,
        open val ne: MacroCell,
        open val sw: MacroCell,
        open val se: MacroCell,
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

        /**
         * A non-leaf [MacroCell], which contains 4 subnode [MacroCell]s.
         */
        data class CellNodeLevel1(
            override val nw: Cell,
            override val ne: Cell,
            override val sw: Cell,
            override val se: Cell,
        ) : CellNode(nw, ne, sw, se) {
            val shortPackedValue =
                ((if (nw.isAlive) 1 shl 0 else 0) or
                    (if (ne.isAlive) 1 shl 1 else 0) or
                    (if (sw.isAlive) 1 shl 2 else 0) or
                    (if (se.isAlive) 1 shl 3 else 0)).toUShort()
        }

        /**
         * A non-leaf [MacroCell], which contains 4 subnode [MacroCell]s.
         */
        data class CellNodeLevel2(
            override val nw: CellNodeLevel1,
            override val ne: CellNodeLevel1,
            override val sw: CellNodeLevel1,
            override val se: CellNodeLevel1,
        ) : CellNode(nw, ne, sw, se) {
            val shortPackedValue =
                ((if (nw.nw.isAlive) 1 shl 0 else 0) or
                    (if (nw.ne.isAlive) 1 shl 1 else 0) or
                    (if (nw.sw.isAlive) 1 shl 2 else 0) or
                    (if (nw.se.isAlive) 1 shl 3 else 0) or
                    (if (ne.nw.isAlive) 1 shl 4 else 0) or
                    (if (ne.ne.isAlive) 1 shl 5 else 0) or
                    (if (ne.sw.isAlive) 1 shl 6 else 0) or
                    (if (ne.se.isAlive) 1 shl 7 else 0) or
                    (if (sw.nw.isAlive) 1 shl 8 else 0) or
                    (if (sw.ne.isAlive) 1 shl 9 else 0) or
                    (if (sw.sw.isAlive) 1 shl 10 else 0) or
                    (if (sw.se.isAlive) 1 shl 11 else 0) or
                    (if (se.nw.isAlive) 1 shl 12 else 0) or
                    (if (se.ne.isAlive) 1 shl 13 else 0) or
                    (if (se.sw.isAlive) 1 shl 14 else 0) or
                    (if (se.se.isAlive) 1 shl 15 else 0)).toUShort()
        }

        /**
         * A non-leaf [MacroCell], which contains 4 subnode [MacroCell]s.
         */
        data class CellNodeLevelN(
            override val nw: CellNode,
            override val ne: CellNode,
            override val sw: CellNode,
            override val se: CellNode,
        ) : CellNode(nw, ne, sw, se) {
            init {
                check(level >= 3)
            }
        }

        companion object {
            operator fun invoke(
                nw: MacroCell,
                ne: MacroCell,
                sw: MacroCell,
                se: MacroCell,
            ): CellNode =
                when (nw) {
                    is Cell -> {
                        ne as Cell
                        sw as Cell
                        se as Cell
                        CellNodeLevel1(nw, ne, sw, se)
                    }
                    is CellNodeLevel1 -> {
                        ne as CellNodeLevel1
                        sw as CellNodeLevel1
                        se as CellNodeLevel1
                        CellNodeLevel2(nw, ne, sw, se)
                    }
                    is CellNodeLevel2,
                    is CellNodeLevelN,
                    -> {
                        nw as CellNode
                        ne as CellNode
                        sw as CellNode
                        se as CellNode
                        CellNodeLevelN(nw, ne, sw, se)
                    }
                }
        }
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
                    CellNode(nw = nw.withCell(target, isAlive), ne = ne, sw = sw, se = se)
                } else {
                    CellNode(nw = nw, ne = ne.withCell(target + IntOffset(-offsetDiff, 0), isAlive), sw = sw, se = se)
                }
            } else {
                if (isWest) {
                    CellNode(nw = nw, ne = ne, sw = sw.withCell(target + IntOffset(0, -offsetDiff), isAlive), se = se)
                } else {
                    CellNode(
                        nw = nw,
                        ne = ne,
                        sw = sw,
                        se = se.withCell(target + IntOffset(-offsetDiff, -offsetDiff), isAlive),
                    )
                }
            }
        }
    }
}

/**
 * Creates a [MacroCell] with the given [level] as a window looking into [CellState] at [offset].
 */
fun createMacroCell(cellState: CellState, offset: IntOffset, level: Int): MacroCell = if (level == 0) {
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
        CellNode(smallerEmptyMacroCell, smallerEmptyMacroCell, smallerEmptyMacroCell, smallerEmptyMacroCell)
    }
}

/**
 * Returns an [Iterator] of [IntOffset] for every alive cell within the [cellWindow] represented by this [MacroCell],
 * with the given upper left corner [offset].
 */
fun MacroCell.iterator(
    offset: IntOffset,
    cellWindow: IntRect,
): Iterator<IntOffset> {
    val macroCell = this
    return iterator {
        @Suppress("ComplexCondition")
        if (
            size > 0 &&
            cellWindow.right >= 0 &&
            cellWindow.bottom >= 0 &&
            cellWindow.left < 1 shl level &&
            cellWindow.top < 1 shl level
        ) {
            when (macroCell) {
                AliveCell -> yield(offset)
                DeadCell -> throw AssertionError("Dead cell must have a size equal to 0!")
                is CellNode -> {
                    val offsetDiff = 1 shl (level - 1)
                    yieldAll(macroCell.nw.iterator(offset, cellWindow))
                    yieldAll(
                        macroCell.ne.iterator(
                            offset + IntOffset(offsetDiff, 0),
                            cellWindow.translate(IntOffset(-offsetDiff, 0)),
                        ),
                    )
                    yieldAll(
                        macroCell.sw.iterator(
                            offset + IntOffset(0, offsetDiff),
                            cellWindow.translate(IntOffset(0, -offsetDiff)),
                        ),
                    )
                    yieldAll(
                        macroCell.se.iterator(
                            offset + IntOffset(offsetDiff, offsetDiff),
                            cellWindow.translate(IntOffset(-offsetDiff, -offsetDiff)),
                        ),
                    )
                }
            }
        }
    }
}

/**
 * Returns an [Iterator] of [IntOffset] for every alive cell within the [cellWindow] represented by this [MacroCell],
 * with the given upper left corner [offset].
 */
fun MacroCell.shortPackedIterator(
    metaOffset: IntOffset,
    metaWindow: IntRect,
): Iterator<Pair<IntOffset, UShort>> {
    val macroCell = this
    return iterator {
        @Suppress("ComplexCondition")
        if (size == 0) return@iterator

        if ()

        if (
            size > 0 &&
            metaWindow.right >= 0 &&
            metaWindow.bottom >= 0 &&
            metaWindow.left < 1 shl level &&
            metaWindow.top < 1 shl level
        ) {
            when (macroCell) {
                AliveCell -> yield(offset)
                DeadCell -> throw AssertionError("Dead cell must have a size equal to 0!")
                is CellNode -> {
                    val offsetDiff = 1 shl (level - 1)
                    yieldAll(macroCell.nw.iterator(offset, cellWindow))
                    yieldAll(
                        macroCell.ne.iterator(
                            offset + IntOffset(offsetDiff, 0),
                            cellWindow.translate(IntOffset(-offsetDiff, 0)),
                        ),
                    )
                    yieldAll(
                        macroCell.sw.iterator(
                            offset + IntOffset(0, offsetDiff),
                            cellWindow.translate(IntOffset(0, -offsetDiff)),
                        ),
                    )
                    yieldAll(
                        macroCell.se.iterator(
                            offset + IntOffset(offsetDiff, offsetDiff),
                            cellWindow.translate(IntOffset(-offsetDiff, -offsetDiff)),
                        ),
                    )
                }
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

/**
 * An optimized version of [contains] for a collection of [targets].
 *
 * This runs in O(targets.size * level) time.
 */
@Suppress("ReturnCount")
fun MacroCell.containsAll(targets: Collection<IntOffset>): Boolean {
    // Fast path: vacuously true
    if (targets.isEmpty()) return true

    // Fast path: if our size is less than the total number of targets, we can't possibly contain all
    if (size < targets.size) return false

    // Invariant: if size was zero, but size < targets.size, then targets.size == 0, so we also should have returned
    check(size > 0)

    // We can't contain targets outside of the representation
    if (targets.any { target -> target.x !in 0 until (1 shl level) || target.y !in 0 until (1 shl level) })
        return false

    return when (this) {
        AliveCell -> {
            check(targets.size == 1)
            check(targets.first() == IntOffset.Zero)
            true
        }
        DeadCell -> {
            throw AssertionError("Dead cell must have a size equal to 0!")
        }
        is CellNode -> {
            val offsetDiff = 1 shl (level - 1)
            val (northTargets, southTargets) = targets.partition { target ->
                target.y < offsetDiff
            }
            val (northWestTargets, northEastTargets) = northTargets.partition { target ->
                target.x < offsetDiff
            }
            val (southWestTargets, southEastTargets) = southTargets.partition { target ->
                target.x < offsetDiff
            }
            // Recurse on subtrees
            nw.containsAll(northWestTargets) &&
                ne.containsAll(northEastTargets.map { it + IntOffset(-offsetDiff, 0) }) &&
                sw.containsAll(southWestTargets.map { it + IntOffset(0, -offsetDiff) }) &&
                se.containsAll(southEastTargets.map { it + IntOffset(-offsetDiff, -offsetDiff) })
        }
    }
}
