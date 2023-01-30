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

package com.alexvanyo.composelife.ui.util

import kotlin.test.Test
import kotlin.test.assertEquals

class LerpTests {

    @Test
    fun start_is_correct_value() {
        assertEquals(
            5f,
            lerp(
                startValue = 5f,
                endValue = 10f,
                fraction = 0f,
            )
        )
    }

    @Test
    fun end_is_correct_value() {
        assertEquals(
            10f,
            lerp(
                startValue = 5f,
                endValue = 10f,
                fraction = 1f,
            )
        )
    }

    @Test
    fun midpoint_is_correct_value() {
        assertEquals(
            7.5f,
            lerp(
                startValue = 5f,
                endValue = 10f,
                fraction = 0.5f,
            )
        )
    }
}
