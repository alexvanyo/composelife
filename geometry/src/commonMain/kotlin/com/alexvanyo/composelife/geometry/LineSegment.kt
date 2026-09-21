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

import kotlin.math.max
import kotlin.math.min

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

internal fun cellIntersections(start: Offset, end: Offset, destination: MutableSet<IntOffset>) {
    val startCell = floor(start)
    val endCell = floor(end)

    destination.add(startCell)
    destination.add(endCell)

    val minX = min(startCell.x, endCell.x)
    val maxX = max(startCell.x, endCell.x)
    val minY = min(startCell.y, endCell.y)
    val maxY = max(startCell.y, endCell.y)

    for (x in minX..maxX) {
        for (y in minY..maxY) {
            val cell = IntOffset(x, y)
            if (cell != startCell && cell != endCell && isActiveIntersectedCell(cell, start, end)) {
                destination.add(cell)
            }
        }
    }
}

@Suppress("ReturnCount")
private fun isActiveIntersectedCell(cell: IntOffset, start: Offset, end: Offset): Boolean {
    val dx = end.x - start.x
    val dy = end.y - start.y
    val cx0 = cell.x.toFloat()
    val cx1 = (cell.x + 1).toFloat()
    val cy0 = cell.y.toFloat()
    val cy1 = (cell.y + 1).toFloat()

    val tx0: Float
    val tx1: Float
    if (dx == 0f) {
        if (start.x < cx0 || start.x > cx1) return false
        tx0 = 0f
        tx1 = 1f
    } else if (dx > 0f) {
        tx0 = (cx0 - start.x) / dx
        tx1 = (cx1 - start.x) / dx
    } else {
        tx0 = (cx1 - start.x) / dx
        tx1 = (cx0 - start.x) / dx
    }

    val ty0: Float
    val ty1: Float
    if (dy == 0f) {
        if (start.y < cy0 || start.y > cy1) return false
        ty0 = 0f
        ty1 = 1f
    } else if (dy > 0f) {
        ty0 = (cy0 - start.y) / dy
        ty1 = (cy1 - start.y) / dy
    } else {
        ty0 = (cy1 - start.y) / dy
        ty1 = (cy0 - start.y) / dy
    }

    val tEnter = maxOf(0f, maxOf(tx0, ty0))
    val tExit = minOf(1f, minOf(tx1, ty1))

    return tEnter < tExit
}
