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

import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.geometry.Rect
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import androidx.compose.ui.unit.LayoutDirection
import kotlin.test.Test
import kotlin.test.assertEquals

class RectExtensionsTests {

    @Test
    fun rect_times_is_correct() {
        val rect = Rect(1f, 2f, 3f, 4f)
        assertEquals(Rect(2f, 4f, 6f, 8f), rect * 2f)
    }

    @Test
    fun rect_div_is_correct() {
        val rect = Rect(2f, 4f, 6f, 8f)
        assertEquals(Rect(1f, 2f, 3f, 4f), rect / 2f)
    }

    @Test
    fun rect_corners_ltr_are_correct() {
        val rect = Rect(10f, 20f, 30f, 40f)
        assertEquals(Offset(10f, 20f), rect.topStart(LayoutDirection.Ltr))
        assertEquals(Offset(30f, 20f), rect.topEnd(LayoutDirection.Ltr))
        assertEquals(Offset(10f, 30f), rect.centerStart(LayoutDirection.Ltr))
        assertEquals(Offset(30f, 30f), rect.centerEnd(LayoutDirection.Ltr))
        assertEquals(Offset(10f, 40f), rect.bottomStart(LayoutDirection.Ltr))
        assertEquals(Offset(30f, 40f), rect.bottomEnd(LayoutDirection.Ltr))
    }

    @Test
    fun rect_corners_rtl_are_correct() {
        val rect = Rect(10f, 20f, 30f, 40f)
        assertEquals(Offset(30f, 20f), rect.topStart(LayoutDirection.Rtl))
        assertEquals(Offset(10f, 20f), rect.topEnd(LayoutDirection.Rtl))
        assertEquals(Offset(30f, 30f), rect.centerStart(LayoutDirection.Rtl))
        assertEquals(Offset(10f, 30f), rect.centerEnd(LayoutDirection.Rtl))
        assertEquals(Offset(30f, 40f), rect.bottomStart(LayoutDirection.Rtl))
        assertEquals(Offset(10f, 40f), rect.bottomEnd(LayoutDirection.Rtl))
    }

    @Test
    fun int_rect_corners_ltr_are_correct() {
        val rect = IntRect(10, 20, 30, 40)
        assertEquals(IntOffset(10, 20), rect.topStart(LayoutDirection.Ltr))
        assertEquals(IntOffset(30, 20), rect.topEnd(LayoutDirection.Ltr))
        assertEquals(IntOffset(10, 30), rect.centerStart(LayoutDirection.Ltr))
        assertEquals(IntOffset(30, 30), rect.centerEnd(LayoutDirection.Ltr))
        assertEquals(IntOffset(10, 40), rect.bottomStart(LayoutDirection.Ltr))
        assertEquals(IntOffset(30, 40), rect.bottomEnd(LayoutDirection.Ltr))
    }

    @Test
    fun int_rect_corners_rtl_are_correct() {
        val rect = IntRect(10, 20, 30, 40)
        assertEquals(IntOffset(30, 20), rect.topStart(LayoutDirection.Rtl))
        assertEquals(IntOffset(10, 20), rect.topEnd(LayoutDirection.Rtl))
        assertEquals(IntOffset(30, 30), rect.centerStart(LayoutDirection.Rtl))
        assertEquals(IntOffset(10, 30), rect.centerEnd(LayoutDirection.Rtl))
        assertEquals(IntOffset(30, 40), rect.bottomStart(LayoutDirection.Rtl))
        assertEquals(IntOffset(10, 40), rect.bottomEnd(LayoutDirection.Rtl))
    }
}
