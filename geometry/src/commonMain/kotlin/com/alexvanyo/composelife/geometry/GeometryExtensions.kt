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

package com.alexvanyo.composelife.geometry

import kotlin.math.abs
import kotlin.math.floor
import kotlin.math.max
import kotlin.math.sign

/**
 * Floors an [Offset] into discrete [IntOffset] cell coordinates.
 */
fun floor(offset: Offset): IntOffset = IntOffset(
    floor(offset.x).toInt(),
    floor(offset.y).toInt(),
)

/**
 * Calculates the Chebyshev distance represented by this [IntOffset].
 */
fun IntOffset.chebyshevDistance(): Int = max(abs(x), abs(y))

/**
 * Calculates the Manhattan distance represented by this [IntOffset].
 */
fun IntOffset.manhattanDistance(): Int = abs(x) + abs(y)

/**
 * Returns `1.0` if this [Offset] is on the right side of the line (from [start] to [end]), `0.0` if on this line,
 * and `-1.0` if on the left side of the line.
 */
fun Offset.sideOfLine(start: Offset, end: Offset): Float =
    sign((end.x - start.x) * (y - start.y) - (end.y - start.y) * (x - start.x))

/**
 * Returns the 8 diagonal and orthogonal neighbors to the [IntOffset].
 */
fun IntOffset.getMooreNeighbors(): Set<IntOffset> = mooreNeighborOffsets.map { it + this }.toSet()

private val mooreNeighborOffsets = listOf(
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
 * Returns the 4 orthogonal neighbors to the [IntOffset].
 */
fun IntOffset.getVonNeumannNeighbors(): Set<IntOffset> = vonNeumannNeighborOffsets.map { it + this }.toSet()

private val vonNeumannNeighborOffsets = listOf(
    IntOffset(0, -1),
    IntOffset(-1, 0),
    IntOffset(1, 0),
    IntOffset(0, 1),
)
