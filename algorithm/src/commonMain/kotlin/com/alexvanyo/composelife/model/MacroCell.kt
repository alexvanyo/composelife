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
@file:OptIn(ExperimentalUnsignedTypes::class)

package com.alexvanyo.composelife.model

import com.alexvanyo.composelife.geometry.IntOffset

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
 */
typealias LeafNode = ULong
typealias Level4Node = MacroCell.Level4Node
typealias CellNode = MacroCell.CellNode

internal inline fun Level4Node(nw: Long, ne: Long, sw: Long, se: Long): MacroCell.Level4Node =
    MacroCell.Level4Node(nw.toULong(), ne.toULong(), sw.toULong(), se.toULong())

internal inline fun LeafNode(aliveCells: Set<IntOffset>): LeafNode {
    var result = 0uL
    for (target in aliveCells) {
        result = result or target.toMask()
    }
    return result
}

internal inline val LeafNode.size: Int get() = countOneBits()

/**
 * Returns this [MacroCell] with the modification of setting the cell at the given (x, y) coordinates to [isAlive],
 * where (0, 0) refers to the upper left cell of the [MacroCell].
 *
 * This function will return a [MacroCell] with the same level.
 */
internal fun MacroCell.withCell(x: Int, y: Int, isAlive: Boolean): MacroCell {
    val intLevel = level().toInt()
    require(x in 0 until (1 shl intLevel) && y in 0 until (1 shl intLevel))
    return f_Algorithm_macroCellWithCell(this, x, y, isAlive)
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
        f_Algorithm_makeLevel4Node(0uL, 0uL, 0uL, 0uL)
    } else {
        val smallerEmptyMacroCell = createEmptyMacroCell(level - 1)
        f_Algorithm_makeCellNode(
            smallerEmptyMacroCell,
            smallerEmptyMacroCell,
            smallerEmptyMacroCell,
            smallerEmptyMacroCell,
        )
    }
}

internal inline operator fun LeafNode.contains(target: IntOffset): Boolean {
    if (target.x !in 0..7 || target.y !in 0..7) return false
    return f_Algorithm_leafContains(this, target.x.toUInt(), target.y.toUInt())
}

/**
 * Returns true if the given [MacroCell] contains an alive cell at coordinates (x, y), where
 * (0, 0) refers to the upper-left corner of the [MacroCell].
 *
 * This runs in O(level) time.
 */
internal fun MacroCell.contains(x: Int, y: Int): Boolean =
    if (size() == 0uL) false else f_Algorithm_macroCellContains(this, x, y)

internal inline operator fun MacroCell.contains(target: IntOffset): Boolean = contains(target.x, target.y)

/**
 * Converts relative coordinates where `x` and `y` are each in `0..7` into the appropriate [ULong] bit for [LeafNode].
 */
internal inline fun cellToLeafMask(x: Int, y: Int): ULong {
    require(x in 0..7 && y in 0..7)
    return maskArray[y * 8 + x]
}

internal inline fun IntOffset.toMask(): ULong = cellToLeafMask(x, y)

internal val maskArray =
    ulongArrayOf(
        1uL shl 0x00,
        1uL shl 0x01,
        1uL shl 0x04,
        1uL shl 0x05,
        1uL shl 0x10,
        1uL shl 0x11,
        1uL shl 0x14,
        1uL shl 0x15,
        1uL shl 0x02,
        1uL shl 0x03,
        1uL shl 0x06,
        1uL shl 0x07,
        1uL shl 0x12,
        1uL shl 0x13,
        1uL shl 0x16,
        1uL shl 0x17,
        1uL shl 0x08,
        1uL shl 0x09,
        1uL shl 0x0C,
        1uL shl 0x0D,
        1uL shl 0x18,
        1uL shl 0x19,
        1uL shl 0x1C,
        1uL shl 0x1D,
        1uL shl 0x0A,
        1uL shl 0x0B,
        1uL shl 0x0E,
        1uL shl 0x0F,
        1uL shl 0x1A,
        1uL shl 0x1B,
        1uL shl 0x1E,
        1uL shl 0x1F,
        1uL shl 0x20,
        1uL shl 0x21,
        1uL shl 0x24,
        1uL shl 0x25,
        1uL shl 0x30,
        1uL shl 0x31,
        1uL shl 0x34,
        1uL shl 0x35,
        1uL shl 0x22,
        1uL shl 0x23,
        1uL shl 0x26,
        1uL shl 0x27,
        1uL shl 0x32,
        1uL shl 0x33,
        1uL shl 0x36,
        1uL shl 0x37,
        1uL shl 0x28,
        1uL shl 0x29,
        1uL shl 0x2C,
        1uL shl 0x2D,
        1uL shl 0x38,
        1uL shl 0x39,
        1uL shl 0x3C,
        1uL shl 0x3D,
        1uL shl 0x2A,
        1uL shl 0x2B,
        1uL shl 0x2E,
        1uL shl 0x2F,
        1uL shl 0x3A,
        1uL shl 0x3B,
        1uL shl 0x3E,
        1uL shl 0x3F,
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
