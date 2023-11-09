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

package com.alexvanyo.composelife.model

import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import androidx.compose.ui.unit.IntSize
import kotlin.test.Test
import kotlin.test.assertEquals

class CellWindowTests {

    @Test
    fun empty_IntRect_returns_empty_points() {
        assertEquals(
            emptyList(),
            CellWindow(IntRect(IntOffset(2, 2), IntSize(0, 0))).containedPoints(),
        )
    }

    @Test
    fun size_one_IntRect_returns_single_point() {
        assertEquals(
            listOf(IntOffset(2, 2)),
            CellWindow(IntRect(IntOffset(2, 2), IntSize(1, 1))).containedPoints(),
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
            CellWindow(
                IntRect(
                    IntOffset(2, 11),
                    IntOffset(5, 14),
                ),
            ).containedPoints(),
        )
    }
}
