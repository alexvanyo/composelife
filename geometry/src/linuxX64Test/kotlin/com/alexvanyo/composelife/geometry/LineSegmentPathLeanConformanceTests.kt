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

import com.alexvanyo.composelife.geometry.lean.LeanGeometryOracle
import kotlin.random.Random
import kotlin.test.Test
import kotlin.test.assertEquals

class LineSegmentPathLeanConformanceTests {

    private val oracle = LeanGeometryOracle()

    @Test
    fun single_points() {
        val points1 = listOf(Offset(5.3f, 5.3f))
        val expected1 = setOf(IntOffset(5, 5))
        assertEquals(expected1, cellIntersections(points1))
        assertEquals(expected1, oracle.cellIntersectionsPath(points1))

        val points2 = listOf(Offset(5f, 5f))
        val expected2 = setOf(IntOffset(5, 5))
        assertEquals(expected2, cellIntersections(points2))
        assertEquals(expected2, oracle.cellIntersectionsPath(points2))
    }

    @Test
    fun segment_within_same_cell() {
        val start = Offset(2.1f, 3.4f)
        val end = Offset(2.8f, 3.9f)
        val expected = setOf(IntOffset(2, 3))
        assertEquals(expected, cellIntersections(start, end))
        assertEquals(expected, oracle.cellIntersectionsSegment(start, end))
        assertEquals(expected, oracle.cellIntersectionsPath(listOf(start, end)))
    }

    @Test
    fun adjacent_cells() {
        val startH = Offset(1.2f, 2.5f)
        val endH = Offset(2.3f, 2.5f)
        val expectedH = setOf(IntOffset(1, 2), IntOffset(2, 2))
        assertEquals(expectedH, cellIntersections(startH, endH))
        assertEquals(expectedH, oracle.cellIntersectionsSegment(startH, endH))
        assertEquals(expectedH, oracle.cellIntersectionsPath(listOf(startH, endH)))

        val startV = Offset(1.5f, 2.2f)
        val endV = Offset(1.5f, 3.8f)
        val expectedV = setOf(IntOffset(1, 2), IntOffset(1, 3))
        assertEquals(expectedV, cellIntersections(startV, endV))
        assertEquals(expectedV, oracle.cellIntersectionsSegment(startV, endV))
        assertEquals(expectedV, oracle.cellIntersectionsPath(listOf(startV, endV)))
    }

    @Test
    fun grid_aligned_horizontal_and_vertical_lines() {
        val startH1 = Offset(0.5f, 1.0f)
        val endH1 = Offset(3.5f, 1.0f)
        val expectedH1 = setOf(
            IntOffset(0, 1),
            IntOffset(1, 1),
            IntOffset(2, 1),
            IntOffset(3, 1),
        )
        assertEquals(expectedH1, cellIntersections(startH1, endH1))
        assertEquals(expectedH1, oracle.cellIntersectionsSegment(startH1, endH1))
        assertEquals(expectedH1, oracle.cellIntersectionsPath(listOf(startH1, endH1)))

        val startH2 = Offset(1.0f, 1.0f)
        val endH2 = Offset(3.0f, 1.0f)
        val expectedH2 = setOf(
            IntOffset(1, 1),
            IntOffset(2, 1),
            IntOffset(3, 1),
        )
        assertEquals(expectedH2, cellIntersections(startH2, endH2))
        assertEquals(expectedH2, oracle.cellIntersectionsSegment(startH2, endH2))
        assertEquals(expectedH2, oracle.cellIntersectionsPath(listOf(startH2, endH2)))

        val startV1 = Offset(1.0f, 0.5f)
        val endV1 = Offset(1.0f, 3.5f)
        val expectedV1 = setOf(
            IntOffset(1, 0),
            IntOffset(1, 1),
            IntOffset(1, 2),
            IntOffset(1, 3),
        )
        assertEquals(expectedV1, cellIntersections(startV1, endV1))
        assertEquals(expectedV1, oracle.cellIntersectionsSegment(startV1, endV1))
        assertEquals(expectedV1, oracle.cellIntersectionsPath(listOf(startV1, endV1)))

        val startV2 = Offset(1.0f, 1.0f)
        val endV2 = Offset(1.0f, 3.0f)
        val expectedV2 = setOf(
            IntOffset(1, 1),
            IntOffset(1, 2),
            IntOffset(1, 3),
        )
        assertEquals(expectedV2, cellIntersections(startV2, endV2))
        assertEquals(expectedV2, oracle.cellIntersectionsSegment(startV2, endV2))
        assertEquals(expectedV2, oracle.cellIntersectionsPath(listOf(startV2, endV2)))
    }

    @Test
    fun diagonal_segment() {
        val start = Offset(0.5f, 0.5f)
        val end = Offset(2.5f, 2.5f)
        val expected = setOf(
            IntOffset(0, 0),
            IntOffset(1, 1),
            IntOffset(2, 2),
        )
        assertEquals(expected, cellIntersections(start, end))
        assertEquals(expected, oracle.cellIntersectionsSegment(start, end))
        assertEquals(expected, oracle.cellIntersectionsPath(listOf(start, end)))
    }

    @Test
    fun diagonal_corner_crossings_add_only_diagonal_cells() {
        val positiveSlopeStart = Offset(0.25f, 0.25f)
        val positiveSlopeEnd = Offset(1.75f, 1.75f)
        val expectedPositiveSlope = setOf(
            IntOffset(0, 0),
            IntOffset(1, 1),
        )
        assertEquals(expectedPositiveSlope, cellIntersections(positiveSlopeStart, positiveSlopeEnd))
        assertEquals(expectedPositiveSlope, oracle.cellIntersectionsSegment(positiveSlopeStart, positiveSlopeEnd))
        assertEquals(
            expectedPositiveSlope,
            oracle.cellIntersectionsPath(listOf(positiveSlopeStart, positiveSlopeEnd)),
        )

        val negativeSlopeStart = Offset(0.25f, 1.75f)
        val negativeSlopeEnd = Offset(1.75f, 0.25f)
        val expectedNegativeSlope = setOf(
            IntOffset(0, 1),
            IntOffset(1, 0),
        )
        assertEquals(expectedNegativeSlope, cellIntersections(negativeSlopeStart, negativeSlopeEnd))
        assertEquals(expectedNegativeSlope, oracle.cellIntersectionsSegment(negativeSlopeStart, negativeSlopeEnd))
        assertEquals(
            expectedNegativeSlope,
            oracle.cellIntersectionsPath(listOf(negativeSlopeStart, negativeSlopeEnd)),
        )
    }

    @Test
    fun diagonal_off_corner_does_not_add_all_four_cells() {
        val start = Offset(0.25f, 0.35f)
        val end = Offset(1.75f, 1.85f)
        val expected = setOf(
            IntOffset(0, 0),
            IntOffset(1, 1),
            IntOffset(0, 1),
        )
        assertEquals(expected, cellIntersections(start, end))
        assertEquals(expected, oracle.cellIntersectionsSegment(start, end))
        assertEquals(expected, oracle.cellIntersectionsPath(listOf(start, end)))
    }

    @Test
    fun multi_corner_crossings_adds_only_diagonal_cells() {
        val start = Offset(0.5f, 0.5f)
        val end = Offset(3.5f, 3.5f)
        val expected = setOf(
            IntOffset(0, 0),
            IntOffset(1, 1),
            IntOffset(2, 2),
            IntOffset(3, 3),
        )
        assertEquals(expected, cellIntersections(start, end))
        assertEquals(expected, oracle.cellIntersectionsSegment(start, end))
        assertEquals(expected, oracle.cellIntersectionsPath(listOf(start, end)))
    }

    @Test
    fun differential_random_segments() {
        val random = Random(42)
        repeat(500) {
            val x1 = random.nextFloat() * 20f - 10f
            val y1 = random.nextFloat() * 20f - 10f
            val x2 = random.nextFloat() * 20f - 10f
            val y2 = random.nextFloat() * 20f - 10f
            val start = Offset(x1, y1)
            val end = Offset(x2, y2)

            val actual = cellIntersections(start, end)
            val oracleExpected = oracle.cellIntersectionsSegment(start, end)

            assertEquals(
                oracleExpected,
                actual,
                "Mismatch on segment ($x1, $y1) -> ($x2, $y2)",
            )
        }
    }

    @Test
    fun differential_random_paths() {
        val random = Random(123)
        repeat(100) {
            val count = random.nextInt(1, 8)
            val points = List(count) {
                Offset(
                    random.nextFloat() * 20f - 10f,
                    random.nextFloat() * 20f - 10f,
                )
            }

            val actual = cellIntersections(points)
            val oracleExpected = oracle.cellIntersectionsPath(points)

            assertEquals(
                oracleExpected,
                actual,
                "Mismatch on path $points",
            )
        }
    }
}
