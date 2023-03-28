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

import androidx.compose.ui.geometry.Rect
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import kotlin.test.Test
import kotlin.test.assertEquals

class RectExtensionsTests {

    @Test
    fun int_rect_to_rect_is_correct() {
        assertEquals(
            Rect(
                -3f,
                2f,
                -1f,
                4f,
            ),
            IntRect(
                -3,
                2,
                -1,
                4,
            ).toRect(),
        )
    }

    @Test
    fun empty_IntRect_returns_single_point() {
        assertEquals(
            listOf(IntOffset(2, 2)),
            IntRect(IntOffset(2, 2), 0).containedPoints(),
        )
    }

    @Test
    fun non_empty_IntRect_returns_correct_order() {
        assertEquals(
            listOf(
                IntOffset(2, 11),
                IntOffset(3, 11),
                IntOffset(4, 11),
                IntOffset(2, 12),
                IntOffset(3, 12),
                IntOffset(4, 12),
                IntOffset(2, 13),
                IntOffset(3, 13),
                IntOffset(4, 13),
            ),
            IntRect(
                IntOffset(2, 11),
                IntOffset(4, 13),
            ).containedPoints(),
        )
    }
}
