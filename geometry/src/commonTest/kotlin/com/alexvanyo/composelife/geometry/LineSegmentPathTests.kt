/*
 * Copyright 2023 The Android Open Source Project
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

import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.geometry.Rect
import androidx.compose.ui.geometry.Size
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.toOffset
import kotlin.math.max
import kotlin.math.min
import kotlin.random.Random
import kotlin.test.Test
import kotlin.test.assertEquals

class LineSegmentPathTests {

    @Test
    fun single_point() {
        assertEquals(
            setOf(IntOffset(5, 5)),
            LineSegmentPath(
                listOf(
                    Offset(5.3f, 5.3f)
                )
            ).cellIntersections()
        )
    }

    @Test
    fun single_point_on_edge() {
        assertEquals(
            setOf(IntOffset(5, 5)),
            LineSegmentPath(
                listOf(
                    Offset(5f, 5f)
                )
            ).cellIntersections()
        )
    }

    @Test
    fun single_line_segment_in_same_cell() {
        assertEquals(
            setOf(IntOffset(5, 5)),
            LineSegmentPath(
                listOf(
                    Offset(5.3f, 5.3f),
                    Offset(5.7f, 5.7f),
                )
            ).cellIntersections()
        )
    }

    @Test
    fun single_line_segment_across_horizontal_cells_east() {
        assertEquals(
            setOf(
                IntOffset(5, 5),
                IntOffset(6, 5),
            ),
            LineSegmentPath(
                listOf(
                    Offset(5.3f, 5.3f),
                    Offset(6.7f, 5.7f),
                )
            ).cellIntersections()
        )
    }

    @Test
    fun single_line_segment_across_horizontal_cells_west() {
        assertEquals(
            setOf(
                IntOffset(5, 5),
                IntOffset(4, 5),
            ),
            LineSegmentPath(
                listOf(
                    Offset(5.3f, 5.3f),
                    Offset(4.7f, 5.7f),
                )
            ).cellIntersections()
        )
    }

    @Test
    fun single_line_segment_across_vertical_cells_south() {
        assertEquals(
            setOf(
                IntOffset(5, 5),
                IntOffset(5, 6),
            ),
            LineSegmentPath(
                listOf(
                    Offset(5.3f, 5.3f),
                    Offset(5.7f, 6.7f),
                )
            ).cellIntersections()
        )
    }

    @Test
    fun single_line_segment_across_vertical_cells_north() {
        assertEquals(
            setOf(
                IntOffset(5, 5),
                IntOffset(5, 4),
            ),
            LineSegmentPath(
                listOf(
                    Offset(5.3f, 5.3f),
                    Offset(5.7f, 4.7f),
                )
            ).cellIntersections()
        )
    }

    @Test
    fun single_line_segment_across_southeast_slope_diagonal_bottom() {
        assertEquals(
            setOf(
                IntOffset(5, 5),
                IntOffset(5, 6),
                IntOffset(6, 6),
            ),
            LineSegmentPath(
                listOf(
                    Offset(5.1f, 5.9f),
                    Offset(6.1f, 6.9f),
                )
            ).cellIntersections()
        )
    }

    @Test
    fun single_line_segment_across_southeast_slope_diagonal_top() {
        assertEquals(
            setOf(
                IntOffset(5, 5),
                IntOffset(6, 5),
                IntOffset(6, 6),
            ),
            LineSegmentPath(
                listOf(
                    Offset(5.9f, 5.1f),
                    Offset(6.9f, 6.1f),
                )
            ).cellIntersections()
        )
    }

    @Test
    fun single_line_segment_across_southeast_slope_diagonal_middle() {
        assertEquals(
            setOf(
                IntOffset(5, 5),
                IntOffset(5, 6),
                IntOffset(6, 5),
                IntOffset(6, 6),
            ),
            LineSegmentPath(
                listOf(
                    Offset(5.5f, 5.5f),
                    Offset(6.5f, 6.5f),
                )
            ).cellIntersections()
        )
    }

    @Test
    fun single_line_segment_across_northeast_slope_diagonal_bottom() {
        assertEquals(
            setOf(
                IntOffset(5, 5),
                IntOffset(6, 5),
                IntOffset(6, 4),
            ),
            LineSegmentPath(
                listOf(
                    Offset(5.9f, 5.9f),
                    Offset(6.9f, 4.9f),
                )
            ).cellIntersections()
        )
    }

    @Test
    fun single_line_segment_across_northeast_slope_diagonal_top() {
        assertEquals(
            setOf(
                IntOffset(5, 5),
                IntOffset(5, 4),
                IntOffset(6, 4),
            ),
            LineSegmentPath(
                listOf(
                    Offset(5.1f, 5.1f),
                    Offset(6.1f, 4.1f),
                )
            ).cellIntersections()
        )
    }

    @Test
    fun single_line_segment_across_northeast_slope_diagonal_middle() {
        assertEquals(
            setOf(
                IntOffset(5, 5),
                IntOffset(5, 4),
                IntOffset(6, 5),
                IntOffset(6, 4),
            ),
            LineSegmentPath(
                listOf(
                    Offset(5.5f, 5.5f),
                    Offset(6.5f, 4.5f),
                )
            ).cellIntersections()
        )
    }

    @Test
    fun single_line_segment_across_northwest_slope_diagonal_bottom() {
        assertEquals(
            setOf(
                IntOffset(5, 5),
                IntOffset(5, 6),
                IntOffset(6, 6),
            ),
            LineSegmentPath(
                listOf(
                    Offset(6.1f, 6.9f),
                    Offset(5.1f, 5.9f),
                )
            ).cellIntersections()
        )
    }

    @Test
    fun single_line_segment_across_northwest_slope_diagonal_top() {
        assertEquals(
            setOf(
                IntOffset(5, 5),
                IntOffset(6, 5),
                IntOffset(6, 6),
            ),
            LineSegmentPath(
                listOf(
                    Offset(5.9f, 5.1f),
                    Offset(6.9f, 6.1f),
                )
            ).cellIntersections()
        )
    }

    @Test
    fun single_line_segment_across_northwest_slope_diagonal_middle() {
        assertEquals(
            setOf(
                IntOffset(5, 5),
                IntOffset(6, 5),
                IntOffset(5, 6),
                IntOffset(6, 6),
            ),
            LineSegmentPath(
                listOf(
                    Offset(6.5f, 6.5f),
                    Offset(5.5f, 5.5f),
                )
            ).cellIntersections()
        )
    }

    @Test
    fun single_line_segment_across_southwest_slope_diagonal_bottom() {
        assertEquals(
            setOf(
                IntOffset(5, 5),
                IntOffset(6, 5),
                IntOffset(6, 4),
            ),
            LineSegmentPath(
                listOf(
                    Offset(6.9f, 4.9f),
                    Offset(5.9f, 5.9f),
                )
            ).cellIntersections()
        )
    }

    @Test
    fun single_line_segment_across_southwest_slope_diagonal_top() {
        assertEquals(
            setOf(
                IntOffset(5, 5),
                IntOffset(5, 4),
                IntOffset(6, 4),
            ),
            LineSegmentPath(
                listOf(
                    Offset(6.1f, 4.1f),
                    Offset(5.1f, 5.1f),
                )
            ).cellIntersections()
        )
    }

    @Test
    fun single_line_segment_across_southwest_slope_diagonal_middle() {
        assertEquals(
            setOf(
                IntOffset(5, 5),
                IntOffset(6, 5),
                IntOffset(5, 4),
                IntOffset(6, 4),
            ),
            LineSegmentPath(
                listOf(
                    Offset(6.5f, 4.5f),
                    Offset(5.5f, 5.5f),
                )
            ).cellIntersections()
        )
    }

    @Test
    fun single_line_segment_across_multiple_cells_horizontal() {
        assertEquals(
            setOf(
                IntOffset(5, 5),
                IntOffset(6, 5),
                IntOffset(7, 5),
                IntOffset(8, 5),
                IntOffset(9, 5),
            ),
            LineSegmentPath(
                listOf(
                    Offset(5.1f, 5.1f),
                    Offset(9.5f, 5.8f),
                )
            ).cellIntersections()
        )
    }

    @Test
    fun single_line_segment_across_multiple_cells_east() {
        assertEquals(
            setOf(
                IntOffset(5, 5),
                IntOffset(6, 5),
                IntOffset(7, 5),
                IntOffset(8, 5),
                IntOffset(9, 5),
            ),
            LineSegmentPath(
                listOf(
                    Offset(5.1f, 5.1f),
                    Offset(9.5f, 5.8f),
                )
            ).cellIntersections()
        )
    }

    @Test
    fun single_line_segment_across_multiple_cells_southwest() {
        assertEquals(
            setOf(
                IntOffset(2, -2),
                IntOffset(1, -2),
                IntOffset(1, -1),
                IntOffset(0, -1),
                IntOffset(0, 0),
                IntOffset(-1, 0),
                IntOffset(-2, 0),
                IntOffset(-2, 1),
                IntOffset(-3, 1),
                IntOffset(-3, 2),
                IntOffset(-4, 2),
                IntOffset(-5, 2),
                IntOffset(-5, 3),
            ),
            LineSegmentPath(
                listOf(
                    Offset(2.1f, -1.2f),
                    Offset(-4.9f, 3.3f),
                )
            ).cellIntersections()
        )
    }

    @Test
    fun random_tests() {
        val random = Random(123)
        repeat(1000) {
            val lineSegmentPath = random.nextLineSegmentPath()
            val expected = lineSegmentPath.bruteForceCellIntersections()
            val actual = lineSegmentPath.cellIntersections()

            assertEquals(
                emptySet(),
                expected - actual,
                "extra in expected for lineSegmentPath: $lineSegmentPath",
            )
            assertEquals(
                emptySet(),
                actual - expected,
                "extra in actual lineSegmentPath: $lineSegmentPath",
            )
        }
    }
}

private fun Random.nextLineSegmentPath(): LineSegmentPath {
    val numberPoints = nextInt(1, 10)
    return LineSegmentPath(List(numberPoints) { nextPoint() })
}

private fun Random.nextPoint(): Offset =
    Offset(
        nextFloat() * 10f,
        nextFloat() * 10f,
    )

/**
 * Returns all cells [IntOffset]s that intersect with the [LineSegmentPath] with a brute force algorithm just for
 * testing.
 */
private fun LineSegmentPath.bruteForceCellIntersections(): Set<IntOffset> =
    if (points.size == 1) {
        setOf(floor(points.first()))
    } else {
        points.zipWithNext { a, b -> bruteForceCellIntersections(a, b) }.flatten().toSet()
    }

private fun bruteForceCellIntersections(start: Offset, end: Offset): Set<IntOffset> =
    buildSet {
        val minX = kotlin.math.floor(min(start.x, end.x)).toInt()
        val maxX = kotlin.math.floor(max(start.x, end.x)).toInt()
        val minY = kotlin.math.floor(min(start.y, end.y)).toInt()
        val maxY = kotlin.math.floor(max(start.y, end.y)).toInt()

        addAll(
            (minX..maxX).flatMap { x ->
                (minY..maxY).map { y ->
                    IntOffset(x, y)
                }
            }
                .filter { it.intersectsLine(start, end) }
        )
    }

private fun IntOffset.intersectsLine(a: Offset, b: Offset) =
    Rect(toOffset(), Size(1f, 1f)).intersectsLine(a, b)

private fun Rect.intersectsLine(a: Offset, b: Offset) =
    contains(a) || contains(b) ||
        doLineSegmentsIntersect(topLeft, topRight, a, b) ||
        doLineSegmentsIntersect(topRight, bottomRight, a, b) ||
        doLineSegmentsIntersect(bottomRight, bottomLeft, a, b) ||
        doLineSegmentsIntersect(bottomLeft, topLeft, a, b)

private fun doLineSegmentsIntersect(a1: Offset, a2: Offset, b1: Offset, b2: Offset): Boolean {
    val b1Sign = b1.sideOfLine(a1, a2)
    val b2Sign = b2.sideOfLine(a1, a2)
    val a1Sign = a1.sideOfLine(b1, b2)
    val a2Sign = a2.sideOfLine(b1, b2)
    return b1Sign * b2Sign <= 0f && a1Sign * a2Sign <= 0f
}
