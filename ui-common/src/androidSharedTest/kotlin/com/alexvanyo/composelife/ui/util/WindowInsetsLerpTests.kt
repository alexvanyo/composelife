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

import androidx.compose.foundation.layout.WindowInsets
import androidx.compose.ui.unit.Density
import androidx.compose.ui.unit.LayoutDirection
import androidx.compose.ui.unit.dp
import kotlin.test.Test
import kotlin.test.assertEquals

class WindowInsetsLerpTests {

    @Test
    fun progress_zero_is_start() {
        val lerpInsets = lerp(
            WindowInsets(left = 5.dp, top = 10.dp, right = 15.dp, bottom = 20.dp),
            WindowInsets(left = 9.dp, top = 14.dp, right = 19.dp, bottom = 24.dp),
            0f,
        )

        val density = Density(1f)

        val left = lerpInsets.getLeft(density, LayoutDirection.Ltr)
        val top = lerpInsets.getTop(density)
        val right = lerpInsets.getRight(density, LayoutDirection.Ltr)
        val bottom = lerpInsets.getBottom(density)

        assertEquals(left, 5)
        assertEquals(top, 10)
        assertEquals(right, 15)
        assertEquals(bottom, 20)
    }

    @Test
    fun progress_one_is_stop() {
        val lerpInsets = lerp(
            WindowInsets(left = 5.dp, top = 10.dp, right = 15.dp, bottom = 20.dp),
            WindowInsets(left = 9.dp, top = 14.dp, right = 19.dp, bottom = 24.dp),
            1f,
        )

        val density = Density(1f)

        val left = lerpInsets.getLeft(density, LayoutDirection.Ltr)
        val top = lerpInsets.getTop(density)
        val right = lerpInsets.getRight(density, LayoutDirection.Ltr)
        val bottom = lerpInsets.getBottom(density)

        assertEquals(left, 9)
        assertEquals(top, 14)
        assertEquals(right, 19)
        assertEquals(bottom, 24)
    }

    @Test
    fun progress_one_quarter_is_correct() {
        val lerpInsets = lerp(
            WindowInsets(left = 5.dp, top = 10.dp, right = 15.dp, bottom = 20.dp),
            WindowInsets(left = 9.dp, top = 14.dp, right = 19.dp, bottom = 24.dp),
            0.25f,
        )

        val density = Density(1f)

        val left = lerpInsets.getLeft(density, LayoutDirection.Ltr)
        val top = lerpInsets.getTop(density)
        val right = lerpInsets.getRight(density, LayoutDirection.Ltr)
        val bottom = lerpInsets.getBottom(density)

        assertEquals(left, 6)
        assertEquals(top, 11)
        assertEquals(right, 16)
        assertEquals(bottom, 21)
    }
}
