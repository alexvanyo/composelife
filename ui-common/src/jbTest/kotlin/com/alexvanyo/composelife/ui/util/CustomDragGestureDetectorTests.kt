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

import androidx.compose.foundation.gestures.Orientation
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.input.pointer.PointerId
import androidx.compose.ui.input.pointer.PointerInputChange
import androidx.compose.ui.input.pointer.PointerType
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertNull
import kotlin.test.assertTrue

class CustomDragGestureDetectorTests {

    private fun createPointerInputChange(
        position: Offset,
        previousPosition: Offset,
        id: PointerId = PointerId(1L),
        pressed: Boolean = true,
    ): PointerInputChange = PointerInputChange(
        id = id,
        uptimeMillis = 0L,
        position = position,
        pressed = pressed,
        pressure = 1.0f,
        previousUptimeMillis = 0L,
        previousPosition = previousPosition,
        previousPressed = true,
        isInitiallyConsumed = false,
        type = PointerType.Touch,
        scrollDelta = Offset.Zero,
        scaleFactor = 1.0f,
        panOffset = Offset.Zero,
    )

    @Test
    fun null_orientation_below_touch_slop_returns_null() {
        val detector = TouchSlopDetector(orientation = null)
        val event = createPointerInputChange(
            position = Offset(5f, 0f),
            previousPosition = Offset(0f, 0f),
        )
        assertNull(detector.addPointerInputChange(event, touchSlop = 10f))
    }

    @Test
    fun null_orientation_above_touch_slop_returns_post_slop_offset() {
        val detector = TouchSlopDetector(orientation = null)
        val event = createPointerInputChange(
            position = Offset(20f, 0f),
            previousPosition = Offset(0f, 0f),
        )
        val result = detector.addPointerInputChange(event, touchSlop = 10f)
        assertEquals(Offset(10f, 0f), result)
    }

    @Test
    fun reset_clears_accumulated_position_change() {
        val detector = TouchSlopDetector(orientation = null)
        val event1 = createPointerInputChange(
            position = Offset(8f, 0f),
            previousPosition = Offset(0f, 0f),
        )
        detector.addPointerInputChange(event1, touchSlop = 10f)
        detector.reset()

        val event2 = createPointerInputChange(
            position = Offset(5f, 0f),
            previousPosition = Offset(0f, 0f),
        )
        assertNull(detector.addPointerInputChange(event2, touchSlop = 10f))
    }

    @Test
    fun horizontal_orientation_main_and_cross_axis_are_correct() {
        val detector = TouchSlopDetector(orientation = Orientation.Horizontal)
        with(detector) {
            val offset = Offset(10f, 20f)
            assertEquals(10f, offset.mainAxis())
            assertEquals(20f, offset.crossAxis())
        }
    }

    @Test
    fun horizontal_orientation_above_touch_slop_returns_post_slop_offset() {
        val detector = TouchSlopDetector(orientation = Orientation.Horizontal)
        val event = createPointerInputChange(
            position = Offset(25f, 5f),
            previousPosition = Offset(0f, 0f),
        )
        val result = detector.addPointerInputChange(event, touchSlop = 10f)
        assertEquals(Offset(15f, 5f), result)
    }

    @Test
    fun vertical_orientation_main_and_cross_axis_are_correct() {
        val detector = TouchSlopDetector(orientation = Orientation.Vertical)
        with(detector) {
            val offset = Offset(10f, 20f)
            assertEquals(20f, offset.mainAxis())
            assertEquals(10f, offset.crossAxis())
        }
    }

    @Test
    fun vertical_orientation_above_touch_slop_returns_post_slop_offset() {
        val detector = TouchSlopDetector(orientation = Orientation.Vertical)
        val event = createPointerInputChange(
            position = Offset(4f, -30f),
            previousPosition = Offset(0f, 0f),
        )
        val result = detector.addPointerInputChange(event, touchSlop = 10f)
        assertEquals(Offset(4f, -20f), result)
    }
}
