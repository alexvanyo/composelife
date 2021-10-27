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
