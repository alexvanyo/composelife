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

import kotlin.math.absoluteValue

/**
 * Returns all discrete grid [IntOffset]s that intersect with the polyline path defined by [points].
 */
fun cellIntersections(points: List<Offset>): Set<IntOffset> {
    require(points.isNotEmpty()) { "Points cannot be empty!" }
    return buildSet {
        for (i in 0 until points.size - 1) {
            cellIntersections(points[i], points[i + 1], this)
        }
        if (points.size == 1) {
            add(floor(points.first()))
        }
    }
}

/**
 * Returns all discrete grid [IntOffset]s that intersect with the line segment between [start] and [end].
 */
fun cellIntersections(start: Offset, end: Offset): Set<IntOffset> = buildSet {
    cellIntersections(start, end, this)
}

@Suppress("ComplexMethod", "CyclomaticComplexMethod", "LongMethod", "LoopWithTooManyJumpStatements")
internal fun cellIntersections(start: Offset, end: Offset, destination: MutableSet<IntOffset>) {
    val startCell = floor(start)
    val endCell = floor(end)

    destination.add(startCell)
    destination.add(endCell)

    if (startCell == endCell) {
        return
    }

    val dx = end.x - start.x
    val dy = end.y - start.y

    val stepX = if (dx > 0f) {
        1
    } else if (dx < 0f) {
        -1
    } else {
        0
    }
    val stepY = if (dy > 0f) {
        1
    } else if (dy < 0f) {
        -1
    } else {
        0
    }

    var currentX = startCell.x
    var currentY = startCell.y

    val maxSteps = (endCell.x - startCell.x).absoluteValue + (endCell.y - startCell.y).absoluteValue + 2
    var step = 0
    while ((currentX != endCell.x || currentY != endCell.y) && step < maxSteps) {
        step++

        val xb = if (stepX > 0) (currentX + 1).toFloat() else currentX.toFloat()
        val yb = if (stepY > 0) (currentY + 1).toFloat() else currentY.toFloat()

        val absDx = dx.toDouble().absoluteValue
        val absDy = dy.toDouble().absoluteValue

        if (stepX == 0) {
            val remY = (yb.toDouble() - start.y.toDouble()).absoluteValue
            if (remY >= absDy) {
                break
            }
            currentY += stepY
        } else if (stepY == 0) {
            val remX = (xb.toDouble() - start.x.toDouble()).absoluteValue
            if (remX >= absDx) {
                break
            }
            currentX += stepX
        } else {
            val remX = (xb.toDouble() - start.x.toDouble()).absoluteValue
            val remY = (yb.toDouble() - start.y.toDouble()).absoluteValue
            val crossX = remX * absDy
            val crossY = remY * absDx
            val limitCross = absDx * absDy

            if (minOf(crossX, crossY) >= limitCross) {
                break
            }

            if (crossX < crossY) {
                currentX += stepX
            } else if (crossY < crossX) {
                currentY += stepY
            } else {
                currentX += stepX
                currentY += stepY
            }
        }

        destination.add(IntOffset(currentX, currentY))
    }
}
