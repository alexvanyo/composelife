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

internal fun cellIntersections(start: Offset, end: Offset, destination: MutableSet<IntOffset>) {
    val startCell = floor(start)
    val endCell = floor(end)
    val cells = f_Geometry_rayMarchSegmentCoords(
        start.x.toDouble(),
        start.y.toDouble(),
        end.x.toDouble(),
        end.y.toDouble(),
        startCell.x,
        startCell.y,
        endCell.x,
        endCell.y,
    )
    for (cell in cells) {
        val pair = cell as Pair<*, *>
        destination.add(IntOffset(pair.first as Int, pair.second as Int))
    }
}
