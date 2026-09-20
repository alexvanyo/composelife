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

import com.alexvanyo.composelife.geometry.IntOffset
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
     * This number is in the range of `0` and `4^x` (inclusive).
     */
    val size: Int

    /**
     * A leaf [MacroCell], which contains 64 cells encoded in a [Long]. The bit mapping is defined as follows, with
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
     * This mapping allows each 4x4 quadrant of the leaf node to be represented by a 16-bit value, and each
     * quadrant can be extracted by the appropriate masking. Furthermore, each 2x2 quadrant of each 4x4 quadrant can be
     * extracted as a contiguous 4-bit value.
     */
    typealias LeafNode = Long

    /**
     * A [MacroCell] at level 4. This level contains exactly 4 [LeafNode]s.
     */
    data class Level4Node(val nw: LeafNode, val ne: LeafNode, val sw: LeafNode, val se: LeafNode) : MacroCell {
        override val level = 4

        override val size = nw.size + ne.size + sw.size + se.size

        /**
         * Memoize the hashcode.
         */
        private val hashCode =
            run {
                // Multi-linear universal hash across the 4 64-bit quadrants with distinct primes,
                // followed by Stafford's Mix13 / MurmurHash3 64-bit mixer for complete bit avalanche.
                var h = 0x243F6A8885A308D3L +
                    (nw * -0x61c8864680b583ebL) +
                    (ne * -0x40a7b892e31b1a47L) +
                    (sw * -0x6b2fb644ecceee15L) +
                    (se * -0x662d04944d150cb1L)
                h = (h xor (h ushr 30)) * -0x40a7b892e31b1a47L
                h = (h xor (h ushr 27)) * -0x6b2fb644ecceee15L
                (h xor (h ushr 31)).toInt()
            }

        override fun hashCode(): Int = hashCode
    }

    /**
     * A non-leaf [MacroCell], which contains 4 subnode [MacroCell]s.
     */
    data class CellNode(val nw: MacroCell, val ne: MacroCell, val sw: MacroCell, val se: MacroCell) : MacroCell {
        init {
            require(nw.level == ne.level)
            require(ne.level == sw.level)
            require(sw.level == se.level)
        }

        override val level = nw.level + 1

        override val size = nw.size + ne.size + sw.size + se.size

        /**
         * Memoize the hashcode.
         */
        private val hashCode =
            run {
                // Multi-linear universal hash across level and the 4 child hashes with distinct primes,
                // followed by MurmurHash3 fmix32 for complete bit avalanche.
                var h = (level * -0x61c8864f) +
                    (nw.hashCode() * -0x7a143589) +
                    (ne.hashCode() * -0x3d4d51c3) +
                    (sw.hashCode() * 0x27D4EB2F) +
                    (se.hashCode() * 0x165667B1)
                h = (h xor (h ushr 16)) * -0x7a143595
                h = (h xor (h ushr 13)) * -0x3d4d51cb
                h xor (h ushr 16)
            }

        override fun hashCode(): Int = hashCode
    }
}

internal inline fun LeafNode(nw: Int, ne: Int, sw: Int, se: Int): LeafNode = (nw.toLong() and 0xFFFFL) or
    ((ne.toLong() and 0xFFFFL) shl 16) or
    ((sw.toLong() and 0xFFFFL) shl 32) or
    ((se.toLong() and 0xFFFFL) shl 48)

internal inline fun LeafNode(aliveCells: Set<IntOffset>): LeafNode {
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

internal inline val LeafNode.se: Int get() = ((this and -0x1000000000000L) ushr 48).toInt()

internal inline val Int.nw: Int get() = ((this and 0b0000_0000_0000_1111) ushr 0)
internal inline val Int.ne: Int get() = ((this and 0b0000_0000_1111_0000) ushr 4)
internal inline val Int.sw: Int get() = ((this and 0b0000_1111_0000_0000) ushr 8)
internal inline val Int.se: Int get() = ((this and 0b1111_0000_0000_0000) ushr 12)

internal inline fun LeafNode.withCell(x: Int, y: Int, isAlive: Boolean): LeafNode {
    val mask = cellToLeafMask(x, y)
    return if (isAlive) {
        or(mask)
    } else {
        and(mask.inv())
    }
}

internal inline fun LeafNode.withCell(target: IntOffset, isAlive: Boolean): LeafNode =
    withCell(target.x, target.y, isAlive)

/**
 * Returns this [MacroCell] with the modification of setting the cell at the given (x, y) coordinates to [isAlive],
 * where (0, 0) refers to the upper left cell of the [MacroCell].
 *
 * This function will return a [MacroCell] with the same level.
 */
@Suppress("LongMethod")
internal fun MacroCell.withCell(x: Int, y: Int, isAlive: Boolean): MacroCell {
    require(x in 0 until (1 shl level) && y in 0 until (1 shl level))

    val offsetDiff = 1 shl (level - 1)
    val isNorth = y < offsetDiff
    val isWest = x < offsetDiff

    return when (this) {
        is Level4Node -> {
            if (isNorth) {
                if (isWest) {
                    Level4Node(
                        nw = nw.withCell(x, y, isAlive),
                        ne = ne,
                        sw = sw,
                        se = se,
                    )
                } else {
                    Level4Node(
                        nw = nw,
                        ne = ne.withCell(x - offsetDiff, y, isAlive),
                        sw = sw,
                        se = se,
                    )
                }
            } else {
                if (isWest) {
                    Level4Node(
                        nw = nw,
                        ne = ne,
                        sw = sw.withCell(x, y - offsetDiff, isAlive),
                        se = se,
                    )
                } else {
                    Level4Node(
                        nw = nw,
                        ne = ne,
                        sw = sw,
                        se = se.withCell(x - offsetDiff, y - offsetDiff, isAlive),
                    )
                }
            }
        }

        is CellNode -> {
            if (isNorth) {
                if (isWest) {
                    CellNode(
                        nw = nw.withCell(x, y, isAlive),
                        ne = ne,
                        sw = sw,
                        se = se,
                    )
                } else {
                    CellNode(
                        nw = nw,
                        ne = ne.withCell(x - offsetDiff, y, isAlive),
                        sw = sw,
                        se = se,
                    )
                }
            } else {
                if (isWest) {
                    CellNode(
                        nw = nw,
                        ne = ne,
                        sw = sw.withCell(x, y - offsetDiff, isAlive),
                        se = se,
                    )
                } else {
                    CellNode(
                        nw = nw,
                        ne = ne,
                        sw = sw,
                        se = se.withCell(x - offsetDiff, y - offsetDiff, isAlive),
                    )
                }
            }
        }
    }
}

internal inline fun MacroCell.withCell(target: IntOffset, isAlive: Boolean): MacroCell =
    withCell(target.x, target.y, isAlive)

/**
 * Creates an empty [MacroCell] with the given [level].
 *
 * The returned [MacroCell] has [MacroCell.size] `0` (in other words, it is entirely dead).
 */
internal fun createEmptyMacroCell(level: Int): MacroCell {
    require(level >= 4)
    return if (level == 4) {
        Level4Node(0L, 0L, 0L, 0L)
    } else {
        val smallerEmptyMacroCell = createEmptyMacroCell(level - 1)
        CellNode(
            smallerEmptyMacroCell,
            smallerEmptyMacroCell,
            smallerEmptyMacroCell,
            smallerEmptyMacroCell,
        )
    }
}

internal inline operator fun LeafNode.contains(target: IntOffset): Boolean {
    if (target.x !in 0..7 || target.y !in 0..7) return false
    return (this and target.toMask()) != 0L
}

/**
 * Returns true if the given [MacroCell] contains an alive cell at coordinates (x, y), where
 * (0, 0) refers to the upper-left corner of the [MacroCell].
 *
 * This runs in O(level) time.
 */
@Suppress("NestedBlockDepth")
internal tailrec fun MacroCell.contains(x: Int, y: Int): Boolean {
    val offsetDiff = 1 shl (level - 1)
    val isNorth = y < offsetDiff
    val isWest = x < offsetDiff

    return if (size == 0) {
        false
    } else if (x !in 0 until (1 shl level) || y !in 0 until (1 shl level)) {
        false
    } else {
        when (this) {
            is Level4Node -> {
                if (isNorth) {
                    if (isWest) {
                        (nw and cellToLeafMask(x, y)) != 0L
                    } else {
                        (ne and cellToLeafMask(x - offsetDiff, y)) != 0L
                    }
                } else {
                    if (isWest) {
                        (sw and cellToLeafMask(x, y - offsetDiff)) != 0L
                    } else {
                        (se and cellToLeafMask(x - offsetDiff, y - offsetDiff)) != 0L
                    }
                }
            }

            is CellNode -> {
                if (isNorth) {
                    if (isWest) {
                        nw.contains(x, y)
                    } else {
                        ne.contains(x - offsetDiff, y)
                    }
                } else {
                    if (isWest) {
                        sw.contains(x, y - offsetDiff)
                    } else {
                        se.contains(x - offsetDiff, y - offsetDiff)
                    }
                }
            }
        }
    }
}

internal inline operator fun MacroCell.contains(target: IntOffset): Boolean = contains(target.x, target.y)

/**
 * Converts relative coordinates where `x` and `y` are each in `0..7` into the appropriate [Long] bit for [LeafNode].
 */
internal inline fun cellToLeafMask(x: Int, y: Int): Long {
    require(x in 0..7 && y in 0..7)
    return maskArray[y * 8 + x]
}

internal inline fun IntOffset.toMask(): Long = cellToLeafMask(x, y)

internal val maskArray =
    longArrayOf(
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
internal inline fun intOffsetFromBit(bit: Int): IntOffset = intOffsetList[bit]

internal val intOffsetList =
    listOf(
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
