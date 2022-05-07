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

package com.alexvanyo.composelife.util

import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import kotlin.math.abs
import kotlin.math.floor
import kotlin.math.max
import kotlin.math.sqrt

/**
 * Returns all [IntOffset]s that are contained in the [IntRect].
 *
 * This includes all [IntOffset] on the border of the [IntRect] ([IntRect.topLeft], [IntRect.bottomRight], etc.).
 *
 * The points are returned in row-major order.
 */
fun IntRect.containedPoints(): List<IntOffset> =
    (top..bottom).flatMap { row ->
        (left..right).map { column ->
            IntOffset(column, row)
        }
    }

/**
 * Converts a pair of [Int] to an [IntOffset].
 */
fun Pair<Int, Int>.toIntOffset() = IntOffset(first, second)

/**
 * Converts an [IntOffset] to a pair of [Int].
 */
fun IntOffset.toPair() = x to y

/**
 * Returns the 8 diagonal and orthogonal neighbors to the [IntOffset].
 */
fun IntOffset.getNeighbors(): Set<IntOffset> = neighborOffsets.map { it + this }.toSet()

private val neighborOffsets = listOf(
    IntOffset(-1, -1),
    IntOffset(0, -1),
    IntOffset(1, -1),
    IntOffset(-1, 0),
    IntOffset(1, 0),
    IntOffset(-1, 1),
    IntOffset(0, 1),
    IntOffset(1, 1),
)

/**
 * Floors an [Offset] into an [IntOffset], taking the [floor] of both coordinates.
 */
fun floor(offset: Offset): IntOffset = IntOffset(floor(offset.x).toInt(), floor(offset.y).toInt())

/**
 * Maps an [IntOffset] into an [Int] to enumerate the 2d plane.
 *
 * The following is a snapshot of the mapping, with (0, 0) mapping to 0.
 *
 *  9 10 11 12 13
 * 24  1  2  3 14
 * 23  8  0  4 15
 * 22  7  6  5 16
 * 21 20 19 18 17
 */
fun IntOffset.toRingIndex(): Int {
    if (this == IntOffset.Zero) return 0

    val ring = max(abs(x), abs(y))
    val ringMin = (2 * (ring - 1) + 1) * (2 * (ring - 1) + 1)
    val ringMax = (2 * ring + 1) * (2 * ring + 1)
    val ringQ = (ringMax - ringMin) / 4
    val ringQ1 = ringMin + ringQ
    val ringQ2 = ringQ1 + ringQ
    val ringQ3 = ringQ2 + ringQ
    check(ringMax == ringQ3 + ringQ)

    return if (y == -ring) {
        ringMin + (x + ring)
    } else if (x == ring) {
        ringQ1 + (y + ring)
    } else if (y == ring) {
        ringQ2 + (ring - x)
    } else {
        check(x == -ring)
        ringQ3 + (ring - y)
    }
}

/**
 * Maps an [Int] to an [IntOffset] where the [Int] is a ring index enumerating the 2d plane.
 *
 * The following is a snapshot of the mapping, with (0, 0) mapping to 0.
 *
 *  9 10 11 12 13
 * 24  1  2  3 14
 * 23  8  0  4 15
 * 22  7  6  5 16
 * 21 20 19 18 17
 */
fun Int.toRingOffset(): IntOffset {
    if (this == 0) return IntOffset.Zero

    val ring = floor((-4 + sqrt((16 - 16 * (1 - this)).toDouble())) / 8).toInt() + 1
    val ringMin = (2 * (ring - 1) + 1) * (2 * (ring - 1) + 1)
    val ringMax = (2 * ring + 1) * (2 * ring + 1)
    val ringQ = (ringMax - ringMin) / 4
    val ringQ1 = ringMin + ringQ
    val ringQ2 = ringQ1 + ringQ
    val ringQ3 = ringQ2 + ringQ
    check(ringMax == ringQ3 + ringQ)

    return if (this < ringQ1) {
        IntOffset(-ring + this - ringMin, -ring)
    } else if (this < ringQ2) {
        IntOffset(ring, -ring + this - ringQ1)
    } else if (this < ringQ3) {
        IntOffset(ring - this + ringQ2, ring)
    } else {
        check(this < ringMax)
        IntOffset(-ring, ring - this + ringQ3)
    }
}
