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

import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.geometry.Rect
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import androidx.compose.ui.unit.LayoutDirection
import kotlin.test.Test
import kotlin.test.assertEquals

@Suppress("TooManyFunctions")
class LayoutDirectionAwareScopeExtensionsTests {

    private val rect = Rect(
        left = 10f,
        top = 20f,
        right = 50f,
        bottom = 80f,
    )

    private val intRect = IntRect(
        left = 10,
        top = 20,
        right = 50,
        bottom = 80,
    )

    @Test
    fun rect_top_start_ltr() {
        with(TestLayoutDirectionAwareScope(LayoutDirection.Ltr)) {
            assertEquals(Offset(10f, 20f), rect.topStart)
        }
    }

    @Test
    fun rect_top_start_rtl() {
        with(TestLayoutDirectionAwareScope(LayoutDirection.Rtl)) {
            assertEquals(Offset(50f, 20f), rect.topStart)
        }
    }

    @Test
    fun rect_top_end_ltr() {
        with(TestLayoutDirectionAwareScope(LayoutDirection.Ltr)) {
            assertEquals(Offset(50f, 20f), rect.topEnd)
        }
    }

    @Test
    fun rect_top_end_rtl() {
        with(TestLayoutDirectionAwareScope(LayoutDirection.Rtl)) {
            assertEquals(Offset(10f, 20f), rect.topEnd)
        }
    }

    @Test
    fun rect_center_start_ltr() {
        with(TestLayoutDirectionAwareScope(LayoutDirection.Ltr)) {
            assertEquals(Offset(10f, 50f), rect.centerStart)
        }
    }

    @Test
    fun rect_center_start_rtl() {
        with(TestLayoutDirectionAwareScope(LayoutDirection.Rtl)) {
            assertEquals(Offset(50f, 50f), rect.centerStart)
        }
    }

    @Test
    fun rect_center_end_ltr() {
        with(TestLayoutDirectionAwareScope(LayoutDirection.Ltr)) {
            assertEquals(Offset(50f, 50f), rect.centerEnd)
        }
    }

    @Test
    fun rect_center_end_rtl() {
        with(TestLayoutDirectionAwareScope(LayoutDirection.Rtl)) {
            assertEquals(Offset(10f, 50f), rect.centerEnd)
        }
    }

    @Test
    fun rect_bottom_start_ltr() {
        with(TestLayoutDirectionAwareScope(LayoutDirection.Ltr)) {
            assertEquals(Offset(10f, 80f), rect.bottomStart)
        }
    }

    @Test
    fun rect_bottom_start_rtl() {
        with(TestLayoutDirectionAwareScope(LayoutDirection.Rtl)) {
            assertEquals(Offset(50f, 80f), rect.bottomStart)
        }
    }

    @Test
    fun rect_bottom_end_ltr() {
        with(TestLayoutDirectionAwareScope(LayoutDirection.Ltr)) {
            assertEquals(Offset(50f, 80f), rect.bottomEnd)
        }
    }

    @Test
    fun rect_bottom_end_rtl() {
        with(TestLayoutDirectionAwareScope(LayoutDirection.Rtl)) {
            assertEquals(Offset(10f, 80f), rect.bottomEnd)
        }
    }

    @Test
    fun int_rect_top_start_ltr() {
        with(TestLayoutDirectionAwareScope(LayoutDirection.Ltr)) {
            assertEquals(IntOffset(10, 20), intRect.topStart)
        }
    }

    @Test
    fun int_rect_top_start_rtl() {
        with(TestLayoutDirectionAwareScope(LayoutDirection.Rtl)) {
            assertEquals(IntOffset(50, 20), intRect.topStart)
        }
    }

    @Test
    fun int_rect_top_end_ltr() {
        with(TestLayoutDirectionAwareScope(LayoutDirection.Ltr)) {
            assertEquals(IntOffset(50, 20), intRect.topEnd)
        }
    }

    @Test
    fun int_rect_top_end_rtl() {
        with(TestLayoutDirectionAwareScope(LayoutDirection.Rtl)) {
            assertEquals(IntOffset(10, 20), intRect.topEnd)
        }
    }

    @Test
    fun int_rect_center_start_ltr() {
        with(TestLayoutDirectionAwareScope(LayoutDirection.Ltr)) {
            assertEquals(IntOffset(10, 50), intRect.centerStart)
        }
    }

    @Test
    fun int_rect_center_start_rtl() {
        with(TestLayoutDirectionAwareScope(LayoutDirection.Rtl)) {
            assertEquals(IntOffset(50, 50), intRect.centerStart)
        }
    }

    @Test
    fun int_rect_center_end_ltr() {
        with(TestLayoutDirectionAwareScope(LayoutDirection.Ltr)) {
            assertEquals(IntOffset(50, 50), intRect.centerEnd)
        }
    }

    @Test
    fun int_rect_center_end_rtl() {
        with(TestLayoutDirectionAwareScope(LayoutDirection.Rtl)) {
            assertEquals(IntOffset(10, 50), intRect.centerEnd)
        }
    }

    @Test
    fun int_rect_bottom_start_ltr() {
        with(TestLayoutDirectionAwareScope(LayoutDirection.Ltr)) {
            assertEquals(IntOffset(10, 80), intRect.bottomStart)
        }
    }

    @Test
    fun int_rect_bottom_start_rtl() {
        with(TestLayoutDirectionAwareScope(LayoutDirection.Rtl)) {
            assertEquals(IntOffset(50, 80), intRect.bottomStart)
        }
    }

    @Test
    fun int_rect_bottom_end_ltr() {
        with(TestLayoutDirectionAwareScope(LayoutDirection.Ltr)) {
            assertEquals(IntOffset(50, 80), intRect.bottomEnd)
        }
    }

    @Test
    fun int_rect_bottom_end_rtl() {
        with(TestLayoutDirectionAwareScope(LayoutDirection.Rtl)) {
            assertEquals(IntOffset(10, 80), intRect.bottomEnd)
        }
    }
}

private class TestLayoutDirectionAwareScope(override val layoutDirection: LayoutDirection) : LayoutDirectionAwareScope
