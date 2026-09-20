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
    return if (points.size == 1) {
        setOf(floor(points.first()))
    } else {
        points.zipWithNext { a, b -> cellIntersections(a, b) }.flatten().toSet()
    }
}

/**
 * Returns all discrete grid [IntOffset]s that intersect with the line segment from [start] to [end].
 */
@Suppress("LongMethod")
fun cellIntersections(start: Offset, end: Offset): Set<IntOffset> = buildSet {
    val startCell = floor(start)
    val endCell = floor(end)

    add(startCell)
    add(endCell)

    val startToEndDiff = startCell - endCell
    val chebyshevDistance = startToEndDiff.chebyshevDistance()
    val manhattanDistance = startToEndDiff.manhattanDistance()
    val isWest = sign(start.x - end.x)
    val isNorth = sign(start.y - end.y)

    // Fast paths
    if (manhattanDistance == 0) {
        // The start and end cells are the same, so we are done
        return@buildSet
    } else if (manhattanDistance == 1) {
        // The start and end cells are the only two cells, so we are done
        return@buildSet
    } else if (chebyshevDistance == 1) {
        // There are only 3 cells: start, end, and one of their shared neighbors, depending on precisely
        // where the start and end points are
        val side = Offset(
            floor(max(start.x, end.x)),
            floor(max(start.y, end.y)),
        ).sideOfLine(start, end)
        val combinedSign = side * isWest * isNorth

        if (combinedSign <= 0f) {
            add(IntOffset(startCell.x, endCell.y))
        }
        if (combinedSign >= 0f) {
            add(IntOffset(endCell.x, startCell.y))
        }
        return@buildSet
    }

    val vector = end - start
    val distance = vector.getDistance()
    check(distance >= 1f)
    val normalizedVector = vector / distance

    val xStep = 1 / normalizedVector.x
    val yStep = 1 / normalizedVector.y

    val tXSequence = generateSequence(
        xStep * if (isWest > 0f) {
            floor(start.x) - start.x
        } else {
            ceil(start.x) - start.x
        },
    ) { it + abs(xStep) }
    val tYSequence = generateSequence(
        yStep * if (isNorth > 0f) {
            floor(start.y) - start.y
        } else {
            ceil(start.y) - start.y
        },
    ) { it + abs(yStep) }

    val tSequence = sequence {
        val tXIterator = tXSequence.iterator()
        val tYIterator = tYSequence.iterator()

        var nextX = tXIterator.next()
        var nextY = tYIterator.next()

        while (true) {
            if (nextX < nextY) {
                yield(nextX to true)
                nextX = tXIterator.next()
            } else {
                yield(nextY to false)
                nextY = tYIterator.next()
            }
        }
    }

    addAll(
        tSequence
            .takeWhile { (t, _) -> t < distance }
            .flatMap { (t, isX) ->
                val offset = lerp(start, end, t / distance)
                if (isX) {
                    listOf(
                        IntOffset(
                            offset.x.roundToInt(),
                            floor(offset.y).roundToInt(),
                        ),
                        IntOffset(
                            offset.x.roundToInt() - 1,
                            floor(offset.y).roundToInt(),
                        ),
                    )
                } else {
                    listOf(
                        IntOffset(
                            floor(offset.x).roundToInt(),
                            offset.y.roundToInt(),
                        ),
                        IntOffset(
                            floor(offset.x).roundToInt(),
                            offset.y.roundToInt() - 1,
                        ),
                    )
                }
            },
    )
}
