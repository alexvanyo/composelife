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
import kotlin.math.ceil
import kotlin.math.floor
import kotlin.math.max
import kotlin.math.roundToInt
import kotlin.math.sign

/**
 * Returns all discrete grid [IntOffset]s that intersect with the polyline path defined by [points].
 */
fun cellIntersections(points: List<Offset>): Set<IntOffset> {
    require(points.isNotEmpty())
    if (points.size == 1) {
        return setOf(floor(points[0]))
    }
    val result = mutableSetOf<IntOffset>()
    for (i in 0 until points.size - 1) {
        cellIntersections(points[i], points[i + 1], result)
    }
    return result
}

/**
 * Returns all discrete grid [IntOffset]s that intersect with the line segment from [start] to [end].
 */
fun cellIntersections(start: Offset, end: Offset): Set<IntOffset> = buildSet {
    cellIntersections(start, end, this)
}

@Suppress("LongMethod", "ComplexMethod", "CyclomaticComplexMethod", "ReturnCount")
internal fun cellIntersections(start: Offset, end: Offset, destination: MutableSet<IntOffset>) {
    val startCell = floor(start)
    val endCell = floor(end)

    destination.add(startCell)
    destination.add(endCell)

    val startToEndDiff = startCell - endCell
    val chebyshevDistance = startToEndDiff.chebyshevDistance()
    val manhattanDistance = startToEndDiff.manhattanDistance()
    val isWest = sign(start.x - end.x)
    val isNorth = sign(start.y - end.y)

    // Fast paths
    if (manhattanDistance <= 1) {
        return
    } else if (chebyshevDistance == 1) {
        val corner = Offset(
            floor(max(start.x, end.x)),
            floor(max(start.y, end.y)),
        )
        val side = corner.sideOfLine(start, end)
        val combinedSign = side * isWest * isNorth

        if (combinedSign < 0f) {
            destination.add(IntOffset(startCell.x, endCell.y))
        } else if (combinedSign > 0f) {
            destination.add(IntOffset(endCell.x, startCell.y))
        }
        return
    }

    val vector = end - start
    val distance = vector.getDistance()
    check(distance >= 1f)
    val normalizedVector = vector / distance

    val xStep = if (normalizedVector.x != 0f) 1f / normalizedVector.x else Float.POSITIVE_INFINITY
    val yStep = if (normalizedVector.y != 0f) 1f / normalizedVector.y else Float.POSITIVE_INFINITY

    val absXStep = abs(xStep)
    val absYStep = abs(yStep)

    var tX = if (normalizedVector.x == 0f) {
        Float.POSITIVE_INFINITY
    } else {
        xStep * initialDelta(start.x, isWest)
    }
    var tY = if (normalizedVector.y == 0f) {
        Float.POSITIVE_INFINITY
    } else {
        yStep * initialDelta(start.y, isNorth)
    }

    while (true) {
        val isCorner = tX == tY
        val nextT = if (tX <= tY) tX else tY
        if (nextT >= distance) {
            break
        }
        val offset = lerp(start, end, nextT / distance)
        if (isCorner) {
            val rx = offset.x.roundToInt()
            val ry = offset.y.roundToInt()
            val cellX = if (isWest > 0f) rx - 1 else rx
            val cellY = if (isNorth > 0f) ry - 1 else ry
            destination.add(IntOffset(cellX, cellY))
            tX += absXStep
            tY += absYStep
        } else if (tX < tY) {
            val rx = offset.x.roundToInt()
            val fy = floor(offset.y).roundToInt()
            destination.add(IntOffset(rx, fy))
            destination.add(IntOffset(rx - 1, fy))
            tX += absXStep
        } else {
            val fx = floor(offset.x).roundToInt()
            val ry = offset.y.roundToInt()
            destination.add(IntOffset(fx, ry))
            destination.add(IntOffset(fx, ry - 1))
            tY += absYStep
        }
    }
}

private fun initialDelta(coord: Float, isNegative: Float): Float = if (isNegative > 0f) {
    val f = floor(coord) - coord
    if (f == 0f) -1f else f
} else {
    val c = ceil(coord) - coord
    if (c == 0f) 1f else c
}
