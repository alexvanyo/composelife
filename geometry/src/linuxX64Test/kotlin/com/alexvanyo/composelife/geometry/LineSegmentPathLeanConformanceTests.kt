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
    fun single_point() {
        val points = listOf(Offset(5.3f, 5.3f))
        val expected = setOf(IntOffset(5, 5))
        assertEquals(expected, cellIntersections(points))
        assertEquals(expected, oracle.cellIntersectionsPath(points))
    }

    @Test
    fun single_point_on_edge() {
        val points = listOf(Offset(5f, 5f))
        val expected = setOf(IntOffset(5, 5))
        assertEquals(expected, cellIntersections(points))
        assertEquals(expected, oracle.cellIntersectionsPath(points))
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
    fun adjacent_horizontal_cells() {
        val start = Offset(1.2f, 2.5f)
        val end = Offset(2.3f, 2.5f)
        val expected = setOf(IntOffset(1, 2), IntOffset(2, 2))
        assertEquals(expected, cellIntersections(start, end))
        assertEquals(expected, oracle.cellIntersectionsSegment(start, end))
        assertEquals(expected, oracle.cellIntersectionsPath(listOf(start, end)))
    }

    @Test
    fun adjacent_vertical_cells() {
        val start = Offset(1.5f, 2.2f)
        val end = Offset(1.5f, 3.8f)
        val expected = setOf(IntOffset(1, 2), IntOffset(1, 3))
        assertEquals(expected, cellIntersections(start, end))
        assertEquals(expected, oracle.cellIntersectionsSegment(start, end))
        assertEquals(expected, oracle.cellIntersectionsPath(listOf(start, end)))
    }

    @Test
    fun diagonal_segment() {
        val start = Offset(0.5f, 0.5f)
        val end = Offset(2.5f, 2.5f)
        val expected = setOf(
            IntOffset(0, 0),
            IntOffset(1, 0),
            IntOffset(0, 1),
            IntOffset(1, 1),
            IntOffset(2, 1),
            IntOffset(1, 2),
            IntOffset(2, 2),
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
