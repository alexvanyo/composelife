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

package com.alexvanyo.composelife.ui.util

import androidx.compose.animation.core.Easing
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith

class EasingPiecewiseTests {

    @Test
    fun easing_requires_sorted_keyframes() {
        assertFailsWith<IllegalArgumentException> {
            Easing(
                Easing { 0f },
                0.8f to Easing { 1f },
                0.5f to Easing { 2f },
            )
        }
    }

    @Test
    fun easing_requires_no_duplicate_zero_keyframe() {
        assertFailsWith<IllegalArgumentException> {
            Easing(
                Easing { 0f },
                0.0f to Easing { 1f },
            )
        }
    }

    @Test
    fun piecewise_easing_interpolation_is_correct() {
        val linear = Easing { it }
        val doubleLinear = Easing { it * 2f }

        val piecewiseEasing = Easing(
            linear,
            0.5f to doubleLinear,
        )

        // Segment 1: [0.0, 0.5] mapped through `linear` (which goes 0.0 to 1.0)
        // input 0.0 -> normalized 0.0 -> linear(0.0) = 0.0
        assertEquals(0.0f, piecewiseEasing.transform(0.0f), 1e-5f)
        // input 0.25 -> normalized 0.5 -> linear(0.5) = 0.5
        assertEquals(0.5f, piecewiseEasing.transform(0.25f), 1e-5f)

        // Segment 2: [0.5, 1.0] mapped through `doubleLinear` (which maps fraction to fraction * 2)
        // input 0.5 -> normalized 0.0 -> doubleLinear(0.0) = 0.0
        assertEquals(0.0f, piecewiseEasing.transform(0.5f), 1e-5f)
        // input 0.75 -> normalized 0.5 -> doubleLinear(0.5) = 1.0
        assertEquals(1.0f, piecewiseEasing.transform(0.75f), 1e-5f)
        // input 1.0 -> normalized 1.0 -> doubleLinear(1.0) = 2.0
        assertEquals(2.0f, piecewiseEasing.transform(1.0f), 1e-5f)
    }

    @Test
    fun piecewise_easing_floor_binary_search_works() {
        val linear = Easing { it }
        val doubleLinear = Easing { it * 2f }
        val halvingLinear = Easing { it / 2f }
        val piecewiseEasing = Easing(
            linear,
            0.2f to linear,
            0.5f to doubleLinear,
            0.8f to halvingLinear,
        )

        // Segment 1: [0.0, 0.2] using `linear`
        assertEquals(0.5f, piecewiseEasing.transform(0.1f), 1e-5f)

        // Segment 2: [0.2, 0.5] using `linear`
        assertEquals(0.5f, piecewiseEasing.transform(0.35f), 1e-5f)

        // Segment 3: [0.5, 0.8] using `doubleLinear`
        assertEquals(1.0f, piecewiseEasing.transform(0.65f), 1e-5f)

        // Segment 4: [0.8, 1.0] using `halvingLinear`
        assertEquals(0.25f, piecewiseEasing.transform(0.9f), 1e-5f)

        // Testing index out of bounds paths for value < 0f (floorBinarySearch returns -1)
        assertFailsWith<IndexOutOfBoundsException> {
            piecewiseEasing.transform(-0.1f)
        }
    }
}
