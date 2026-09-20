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

import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith

class LineSegmentTests {

    @Test
    fun empty_points_throws() {
        assertFailsWith<IllegalArgumentException> {
            cellIntersections(emptyList())
        }
    }

    @Test
    fun single_point() {
        assertEquals(
            setOf(IntOffset(5, 5)),
            cellIntersections(listOf(Offset(5.3f, 5.3f))),
        )
    }

    @Test
    fun single_point_on_edge() {
        assertEquals(
            setOf(IntOffset(5, 5)),
            cellIntersections(listOf(Offset(5f, 5f))),
        )
    }

    @Test
    fun segment_within_same_cell() {
        assertEquals(
            setOf(IntOffset(2, 3)),
            cellIntersections(Offset(2.1f, 3.4f), Offset(2.8f, 3.9f)),
        )
    }

    @Test
    fun adjacent_horizontal_cells() {
        assertEquals(
            setOf(IntOffset(1, 2), IntOffset(2, 2)),
            cellIntersections(Offset(1.2f, 2.5f), Offset(2.3f, 2.5f)),
        )
    }

    @Test
    fun adjacent_vertical_cells() {
        assertEquals(
            setOf(IntOffset(1, 2), IntOffset(1, 3)),
            cellIntersections(Offset(1.5f, 2.2f), Offset(1.5f, 3.8f)),
        )
    }

    @Test
    fun diagonal_segment_contains_intermediate_cells() {
        val cells = cellIntersections(Offset(0.5f, 0.5f), Offset(2.5f, 2.5f))
        assertEquals(
            setOf(
                IntOffset(0, 0),
                IntOffset(1, 0),
                IntOffset(0, 1),
                IntOffset(1, 1),
                IntOffset(2, 1),
                IntOffset(1, 2),
                IntOffset(2, 2),
            ),
            cells,
        )
    }
}
