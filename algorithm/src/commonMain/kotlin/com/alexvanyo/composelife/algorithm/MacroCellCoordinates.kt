/*
 * Copyright 2026 The Android Open Source Project
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

package com.alexvanyo.composelife.algorithm

import com.alexvanyo.composelife.geometry.IntOffset
import com.alexvanyo.composelife.model.MacroCell
import com.alexvanyo.composelife.model.f_Algorithm_cellToLeafBitUInt

/**
 * Maps 2D relative coordinates (within `0..7`) to a bit index within an 8x8 Morton leaf node.
 */
internal fun cellToLeafBit(x: Int, y: Int): Int {
    require(x in 0..7 && y in 0..7)
    return f_Algorithm_cellToLeafBitUInt(x.toUInt(), y.toUInt()).toInt()
}

/**
 * Converts a set of [IntOffset]s within an 8x8 region into a 64-bit [Long] leaf node.
 */
internal fun coordinatesToLeaf(coordinates: Set<IntOffset>, offsetX: Int = 0, offsetY: Int = 0): Long {
    var leaf = 0L
    for ((x, y) in coordinates) {
        val localX = x - offsetX
        val localY = y - offsetY
        if (localX in 0..7 && localY in 0..7) {
            val bit = cellToLeafBit(localX, localY)
            leaf = leaf or (1L shl bit)
        }
    }
    return leaf
}

/**
 * Converts a 64-bit [Long] leaf node back into a set of [IntOffset]s offset by [offsetX], [offsetY].
 */
internal fun leafToCoordinates(leaf: Long, offsetX: Int = 0, offsetY: Int = 0): Set<IntOffset> {
    if (leaf == 0L) return emptySet()
    val result = mutableSetOf<IntOffset>()
    for (y in 0..7) {
        for (x in 0..7) {
            val bit = cellToLeafBit(x, y)
            if (((leaf ushr bit) and 1L) != 0L) {
                result.add(IntOffset(x + offsetX, y + offsetY))
            }
        }
    }
    return result
}

/**
 * Converts a set of [IntOffset]s within a 16x16 region into a [MacroCell.Level4Node].
 */
internal fun coordinatesToLevel4(
    coordinates: Set<IntOffset>,
    offsetX: Int = 0,
    offsetY: Int = 0,
): MacroCell.Level4Node = MacroCell.Level4Node(
    nw = coordinatesToLeaf(coordinates, offsetX, offsetY).toULong(),
    ne = coordinatesToLeaf(coordinates, offsetX + 8, offsetY).toULong(),
    sw = coordinatesToLeaf(coordinates, offsetX, offsetY + 8).toULong(),
    se = coordinatesToLeaf(coordinates, offsetX + 8, offsetY + 8).toULong(),
)
