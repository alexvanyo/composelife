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

import androidx.compose.ui.unit.IntSize
import kotlin.test.Test
import kotlin.test.assertEquals

class IntSizeLerpTests {

    @Test
    fun progress_zero_is_start() {
        assertEquals(
            IntSize(5, 5),
            lerp(IntSize(5, 5), IntSize(9, 9), 0f),
        )
    }

    @Test
    fun progress_one_is_stop() {
        assertEquals(
            IntSize(5, 5),
            lerp(IntSize(5, 5), IntSize(9, 9), 0f),
        )
    }

    @Test
    fun progress_one_quarter_is_correct() {
        assertEquals(
            IntSize(6, 6),
            lerp(IntSize(5, 5), IntSize(9, 9), 0.25f),
        )
    }
}
