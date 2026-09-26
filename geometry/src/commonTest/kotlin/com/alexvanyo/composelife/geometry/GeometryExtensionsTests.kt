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

class GeometryExtensionsTests {

    @Test
    fun floor_positive_coordinates() {
        assertEquals(IntOffset(1, 2), floor(Offset(1.2f, 2.8f)))
    }

    @Test
    fun floor_negative_coordinates() {
        assertEquals(IntOffset(-2, -3), floor(Offset(-1.2f, -2.8f)))
    }

    @Test
    fun floor_exact_integers() {
        assertEquals(IntOffset(3, -4), floor(Offset(3f, -4f)))
    }

    @Test
    fun chebyshev_distance() {
        assertEquals(5, IntOffset(3, -5).chebyshevDistance())
        assertEquals(0, IntOffset(0, 0).chebyshevDistance())
        assertEquals(4, IntOffset(-4, 2).chebyshevDistance())
    }

    @Test
    fun manhattan_distance() {
        assertEquals(8, IntOffset(3, -5).manhattanDistance())
        assertEquals(0, IntOffset(0, 0).manhattanDistance())
        assertEquals(6, IntOffset(-4, 2).manhattanDistance())
    }

    @Test
    fun cell_addition_and_subtraction() {
        val a = IntOffset(3, 4)
        val b = IntOffset(1, -2)
        assertEquals(IntOffset(4, 2), a + b)
        assertEquals(IntOffset(2, 6), a - b)
    }

    @Test
    fun side_of_line() {
        val start = Offset(0f, 0f)
        val end = Offset(2f, 2f)
        assertEquals(-1f, Offset(2f, 0f).sideOfLine(start, end))
        assertEquals(1f, Offset(0f, 2f).sideOfLine(start, end))
        assertEquals(0f, Offset(1f, 1f).sideOfLine(start, end))
    }
}
