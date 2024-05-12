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
@file:Suppress("TooManyFunctions", "NOTHING_TO_INLINE")

package com.alexvanyo.composelife.model

import androidx.annotation.IntRange
import androidx.compose.ui.unit.IntOffset
import com.alexvanyo.composelife.model.MacroCell.CellNode
import com.alexvanyo.composelife.model.MacroCell.LeafNode
import com.alexvanyo.composelife.model.MacroCell.Level4Node

/**
 * A quad tree representation of the state of cells.
 *
 * A [MacroCell] is either a [Level4Node] with 4 [LeafNode] children or a [CellNode] with 4 subnodes.
 */
internal sealed interface MacroCell {

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
     * A leaf [MacroCell], which contains 64 cells encoded in a [ULong]. The bit mapping is defined as follows, with
     * the bit index encoded in hexadecimal:
     *
     * ```
     * + ------------+-------------+
     * | 00 01 04 05 | 10 11 14 15 |
     * | 02 03 06 07 | 12 13 16 17 |
     * | 08 09 0C 0D | 18 19 1C 1D |
     * | 0A 0B 0E 0F | 1A 1B 1E 1F |
     * + ------------+-------------+
     * | 20 21 24 25 | 30 31 34 35 |
     * | 22 23 26 27 | 32 33 36 37 |
     * | 28 29 2C 2D | 38 39 3C 3D |
     * | 2A 2B 2E 2F | 3A 3B 3E 3F |
     * + ------------+-------------+
     * ```
     *
     * This mapping allows each 4x4 quadrant of the leaf node to be represented by a 16-bit [UShort] value, and each
     * quadrant can be extracted by the appropriate masking. Furthermore, each 2x2 quadrant of each 4x4 quadrant can be
     * extracted as a contiguous 4-bit value.
     */
    typealias LeafNode = Long

    /**
     * A [MacroCell] at level 4. This level contains exactly 4 [LeafNode]s.
     */
    data class Level4Node(
        val nw: LeafNode,
        val ne: LeafNode,
        val sw: LeafNode,
        val se: LeafNode,
    ) : MacroCell {
        override val level = 4

        override val size = nw.size + ne.size + sw.size + se.size

        /**
         * Memoize the hashcode.
         *
         * TODO: Is there a better hashcode function?
         */
        private val hashCode = run {
            var hash = nw.hashCode()
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

internal inline fun LeafNode(
    nw: Int,
    ne: Int,
    sw: Int,
    se: Int,
): LeafNode = nw.toLong() or
    (ne.toLong() shl 16) or
    (sw.toLong() shl 32) or
    (se.toLong() shl 48)

internal inline fun LeafNode(
    aliveCells: Set<IntOffset>,
): LeafNode {
    var result = 0L
    for (target in aliveCells) {
        result = result or target.toMask()
    }
    return result
}

internal inline val LeafNode.size: Int get() = countOneBits()

internal inline val LeafNode.nw: Int get() = ((this and 0x000000000000FFFFL) ushr 0).toInt()

internal inline val LeafNode.ne: Int get() = ((this and 0x00000000FFFF0000L) ushr 16).toInt()

internal inline val LeafNode.sw: Int get() = ((this and 0x0000FFFF00000000L) ushr 32).toInt()

internal inline val LeafNode.se: Int get() = ((this and 0xFFFF000000000000uL.toLong()) ushr 48).toInt()

internal inline val Int.nw: Int get() = ((this and 0b0000_0000_0000_1111) ushr 0)
internal inline val Int.ne: Int get() = ((this and 0b0000_0000_1111_0000) ushr 4)
internal inline val Int.sw: Int get() = ((this and 0b0000_1111_0000_0000) ushr 8)
internal inline val Int.se: Int get() = ((this and 0b1111_0000_0000_0000) ushr 12)

internal inline fun LeafNode.withCell(target: IntOffset, isAlive: Boolean): LeafNode {
    val mask = target.toMask()
    return if (isAlive) {
        or(mask)
    } else {
        and(mask.inv())
    }
}

/**
 * Returns this [MacroCell] with the modification of setting the cell at the given [target] offset to [isAlive],
 * where [IntOffset.Zero] refers to the upper left cell of the [MacroCell].
 *
 * This function will return a [MacroCell] with the same level. Therefore, [target] must refer to a valid cell
 * contained by this [MacroCell].
 */
@Suppress("LongMethod")
internal fun MacroCell.withCell(target: IntOffset, isAlive: Boolean): MacroCell {
    require(target.x in 0 until (1 shl level) && target.y in 0 until (1 shl level))

    val offsetDiff = 1 shl (level - 1)
    val isNorth = target.y < offsetDiff
    val isWest = target.x < offsetDiff

    return when (this) {
        is Level4Node -> {
            if (isNorth) {
                if (isWest) {
                    Level4Node(
                        nw = nw.withCell(target, isAlive),
                        ne = ne,
                        sw = sw,
                        se = se,
                    )
                } else {
                    Level4Node(
                        nw = nw,
                        ne = ne.withCell(target + IntOffset(-offsetDiff, 0), isAlive),
                        sw = sw,
                        se = se,
                    )
                }
            } else {
                if (isWest) {
                    Level4Node(
                        nw = nw,
                        ne = ne,
                        sw = sw.withCell(target + IntOffset(0, -offsetDiff), isAlive),
                        se = se,
                    )
                } else {
                    Level4Node(
                        nw = nw,
                        ne = ne,
                        sw = sw,
                        se = se.withCell(target + IntOffset(-offsetDiff, -offsetDiff), isAlive),
                    )
                }
            }
        }
        is CellNode -> {
            if (isNorth) {
                if (isWest) {
                    CellNode(
                        nw = nw.withCell(target, isAlive),
                        ne = ne,
                        sw = sw,
                        se = se,
                    )
                } else {
                    CellNode(
                        nw = nw,
                        ne = ne.withCell(target + IntOffset(-offsetDiff, 0), isAlive),
                        sw = sw,
                        se = se,
                    )
                }
            } else {
                if (isWest) {
                    CellNode(
                        nw = nw,
                        ne = ne,
                        sw = sw.withCell(target + IntOffset(0, -offsetDiff), isAlive),
                        se = se,
                    )
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

internal inline fun createLeafNode(
    cellState: CellState,
    offset: IntOffset,
): LeafNode {
    var result = 0L
    for (i in 0..63) {
        val inAliveCells = if ((offset + intOffsetFromBit(i)) in cellState.aliveCells) 1L else 0L
        result += inAliveCells * (1L shl i)
    }
    return result
}

/**
 * Creates a [MacroCell] with the given [level] as a window looking into [CellState] at [offset].
 */
internal fun createMacroCell(
    cellState: CellState,
    offset: IntOffset,
    @IntRange(from = 4) level: Int,
): MacroCell {
    val offsetDiff = 1 shl (level - 1)
    return if (level == 4) {
        Level4Node(
            nw = createLeafNode(cellState, offset),
            ne = createLeafNode(cellState, offset + IntOffset(offsetDiff, 0)),
            sw = createLeafNode(cellState, offset + IntOffset(0, offsetDiff)),
            se = createLeafNode(cellState, offset + IntOffset(offsetDiff, offsetDiff)),
        )
    } else {
        CellNode(
            createMacroCell(cellState, offset, level - 1),
            createMacroCell(cellState, offset + IntOffset(offsetDiff, 0), level - 1),
            createMacroCell(cellState, offset + IntOffset(0, offsetDiff), level - 1),
            createMacroCell(cellState, offset + IntOffset(offsetDiff, offsetDiff), level - 1),
        )
    }
}

/**
 * Creates an empty [MacroCell] with the given [level].
 *
 * The returned [MacroCell] has [MacroCell.size] `0` (in other words, it is entirely dead).
 */
internal fun createEmptyMacroCell(@IntRange(from = 4) level: Int): MacroCell {
    require(level >= 4)
    return if (level == 4) {
        Level4Node(0L, 0L, 0L, 0L)
    } else {
        val smallerEmptyMacroCell = createEmptyMacroCell(level - 1)
        CellNode(smallerEmptyMacroCell, smallerEmptyMacroCell, smallerEmptyMacroCell, smallerEmptyMacroCell)
    }
}

internal suspend inline fun SequenceScope<IntOffset>.yieldLeafNode(
    leafNode: LeafNode,
    offset: IntOffset,
    cellWindow: CellWindow,
) {
    for (i in 0..63) {
        if ((leafNode and (1L shl i)) != 0L) {
            val intOffsetFromBit = intOffsetFromBit(i)
            if (intOffsetFromBit.x in cellWindow.left until cellWindow.right &&
                intOffsetFromBit.y in cellWindow.top until cellWindow.bottom) {
                yield(offset + intOffsetFromBit)
            }
        }
    }
}

/**
 * Returns an [Iterator] of [IntOffset] for every alive cell within the [cellWindow] represented by this [MacroCell],
 * with the given upper left corner [offset].
 */
internal fun MacroCell.iterator(
    offset: IntOffset,
    cellWindow: CellWindow,
): Iterator<IntOffset> {
    val macroCell = this
    val offsetDiff = 1 shl (level - 1)
    return iterator {
        @Suppress("ComplexCondition")
        if (
            size > 0 &&
            cellWindow.right >= 1 &&
            cellWindow.bottom >= 1 &&
            cellWindow.left < 1 shl level &&
            cellWindow.top < 1 shl level
        ) {
            when (macroCell) {
                is Level4Node -> {
                    yieldLeafNode(nw, offset, cellWindow)
                    yieldLeafNode(
                        ne,
                        offset + IntOffset(offsetDiff, 0),
                        cellWindow.translate(IntOffset(-offsetDiff, 0)),
                    )
                    yieldLeafNode(
                        sw,
                        offset + IntOffset(0, offsetDiff),
                        cellWindow.translate(IntOffset(0, -offsetDiff)),
                    )
                    yieldLeafNode(
                        se,
                        offset + IntOffset(offsetDiff, offsetDiff),
                        cellWindow.translate(IntOffset(-offsetDiff, -offsetDiff)),
                    )
                }
                is CellNode -> {
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

internal inline operator fun LeafNode.contains(target: IntOffset): Boolean =
    (this and target.toMask()) != 0L

/**
 * Returns true if the given [MacroCell] contains an alive cell with the given [target] offset, where
 * [IntOffset.Zero] refers to the upper-left corner of the [MacroCell].
 *
 * This runs in O(level) time.
 */
@Suppress("NestedBlockDepth")
internal tailrec operator fun MacroCell.contains(target: IntOffset): Boolean {
    val offsetDiff = 1 shl (level - 1)
    val isNorth = target.y < offsetDiff
    val isWest = target.x < offsetDiff

    return if (size == 0) {
        false
    } else if (target.x !in 0 until (1 shl level) || target.y !in 0 until (1 shl level)) {
        false
    } else {
        when (this) {
            is Level4Node -> {
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
            is CellNode -> {
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

private inline fun LeafNode.containsAll(targets: Collection<IntOffset>): Boolean {
    for (target in targets) {
        if ((this and target.toMask()) == 0L) {
            return false
        }
    }
    return true
}

/**
 * An optimized version of [contains] for a collection of [targets].
 *
 * This runs in O(targets.size * level) time.
 */
@Suppress("ReturnCount")
internal fun MacroCell.containsAll(targets: Collection<IntOffset>): Boolean {
    // Fast path: vacuously true
    if (targets.isEmpty()) return true

    // Fast path: if our size is less than the total number of targets, we can't possibly contain all
    if (size < targets.size) return false

    // Invariant: if size was zero, but size < targets.size, then targets.size == 0, so we also should have returned
    check(size > 0)

    // We can't contain targets outside of the representation
    if (targets.any { target -> target.x !in 0 until (1 shl level) || target.y !in 0 until (1 shl level) }) {
        return false
    }

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
    return when (this) {
        is Level4Node -> {
            nw.containsAll(northWestTargets) &&
                ne.containsAll(northEastTargets.map { it + IntOffset(-offsetDiff, 0) }) &&
                sw.containsAll(southWestTargets.map { it + IntOffset(0, -offsetDiff) }) &&
                se.containsAll(southEastTargets.map { it + IntOffset(-offsetDiff, -offsetDiff) })
        }
        is CellNode -> {
            nw.containsAll(northWestTargets) &&
                ne.containsAll(northEastTargets.map { it + IntOffset(-offsetDiff, 0) }) &&
                sw.containsAll(southWestTargets.map { it + IntOffset(0, -offsetDiff) }) &&
                se.containsAll(southEastTargets.map { it + IntOffset(-offsetDiff, -offsetDiff) })
        }
    }
}

/**
 * Converts a [IntOffset] where `x` and `y` are each in `0..7` into the appropriate [ULong] bit for [LeafNode]
 */
internal inline fun IntOffset.toMask(): Long {
    require(x in 0..7 && y in 0..7)
    return maskArray[y * 8 + x]
}

@OptIn(ExperimentalUnsignedTypes::class)
private val maskArray = longArrayOf(
    1L shl 0x00,
    1L shl 0x01,
    1L shl 0x04,
    1L shl 0x05,
    1L shl 0x10,
    1L shl 0x11,
    1L shl 0x14,
    1L shl 0x15,
    1L shl 0x02,
    1L shl 0x03,
    1L shl 0x06,
    1L shl 0x07,
    1L shl 0x12,
    1L shl 0x13,
    1L shl 0x16,
    1L shl 0x17,
    1L shl 0x08,
    1L shl 0x09,
    1L shl 0x0C,
    1L shl 0x0D,
    1L shl 0x18,
    1L shl 0x19,
    1L shl 0x1C,
    1L shl 0x1D,
    1L shl 0x0A,
    1L shl 0x0B,
    1L shl 0x0E,
    1L shl 0x0F,
    1L shl 0x1A,
    1L shl 0x1B,
    1L shl 0x1E,
    1L shl 0x1F,
    1L shl 0x20,
    1L shl 0x21,
    1L shl 0x24,
    1L shl 0x25,
    1L shl 0x30,
    1L shl 0x31,
    1L shl 0x34,
    1L shl 0x35,
    1L shl 0x22,
    1L shl 0x23,
    1L shl 0x26,
    1L shl 0x27,
    1L shl 0x32,
    1L shl 0x33,
    1L shl 0x36,
    1L shl 0x37,
    1L shl 0x28,
    1L shl 0x29,
    1L shl 0x2C,
    1L shl 0x2D,
    1L shl 0x38,
    1L shl 0x39,
    1L shl 0x3C,
    1L shl 0x3D,
    1L shl 0x2A,
    1L shl 0x2B,
    1L shl 0x2E,
    1L shl 0x2F,
    1L shl 0x3A,
    1L shl 0x3B,
    1L shl 0x3E,
    1L shl 0x3F,
)

/**
 * Converts a bit index into the appropriate [IntOffset] for [LeafNode].
 */
private inline fun intOffsetFromBit(@IntRange(0, 63) bit: Int) =
    intOffsetList[bit]

private val intOffsetList = listOf(
    IntOffset(0, 0),
    IntOffset(1, 0),
    IntOffset(0, 1),
    IntOffset(1, 1),
    IntOffset(2, 0),
    IntOffset(3, 0),
    IntOffset(2, 1),
    IntOffset(3, 1),
    IntOffset(0, 2),
    IntOffset(1, 2),
    IntOffset(0, 3),
    IntOffset(1, 3),
    IntOffset(2, 2),
    IntOffset(3, 2),
    IntOffset(2, 3),
    IntOffset(3, 3),

    IntOffset(4, 0),
    IntOffset(5, 0),
    IntOffset(4, 1),
    IntOffset(5, 1),
    IntOffset(6, 0),
    IntOffset(7, 0),
    IntOffset(6, 1),
    IntOffset(7, 1),
    IntOffset(4, 2),
    IntOffset(5, 2),
    IntOffset(4, 3),
    IntOffset(5, 3),
    IntOffset(6, 2),
    IntOffset(7, 2),
    IntOffset(6, 3),
    IntOffset(7, 3),

    IntOffset(0, 4),
    IntOffset(1, 4),
    IntOffset(0, 5),
    IntOffset(1, 5),
    IntOffset(2, 4),
    IntOffset(3, 4),
    IntOffset(2, 5),
    IntOffset(3, 5),
    IntOffset(0, 6),
    IntOffset(1, 6),
    IntOffset(0, 7),
    IntOffset(1, 7),
    IntOffset(2, 6),
    IntOffset(3, 6),
    IntOffset(2, 7),
    IntOffset(3, 7),

    IntOffset(4, 4),
    IntOffset(5, 4),
    IntOffset(4, 5),
    IntOffset(5, 5),
    IntOffset(6, 4),
    IntOffset(7, 4),
    IntOffset(6, 5),
    IntOffset(7, 5),
    IntOffset(4, 6),
    IntOffset(5, 6),
    IntOffset(4, 7),
    IntOffset(5, 7),
    IntOffset(6, 6),
    IntOffset(7, 6),
    IntOffset(6, 7),
    IntOffset(7, 7),
)
