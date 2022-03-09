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
import kotlin.math.floor

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
    IntOffset(1, 1)
)

/**
 * Floors an [Offset] into an [IntOffset], taking the [floor] of both coordinates.
 */
fun floor(offset: Offset): IntOffset = IntOffset(floor(offset.x).toInt(), floor(offset.y).toInt())
