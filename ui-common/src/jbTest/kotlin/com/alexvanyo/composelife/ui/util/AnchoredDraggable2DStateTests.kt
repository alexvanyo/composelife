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

import androidx.compose.animation.core.snap
import androidx.compose.runtime.saveable.SaverScope
import androidx.compose.ui.geometry.Offset
import kotlinx.coroutines.test.runTest
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.test.assertNotNull

class AnchoredDraggable2DStateTests {

    private enum class TestValue {
        Start,
        Center,
        End,
    }

    private val anchors = DraggableAnchors2D {
        TestValue.Start at Offset(0f, 0f)
        TestValue.Center at Offset(50f, 50f)
        TestValue.End at Offset(100f, 100f)
    }

    @Test
    fun require_offset_throws_when_unspecified() {
        val state = AnchoredDraggable2DState(
            initialValue = TestValue.Start,
            animationSpec = snap(),
        )
        assertFailsWith<IllegalStateException> {
            state.requireOffset()
        }
    }

    @Test
    fun constructor_with_anchors_sets_initial_offset() {
        val state = AnchoredDraggable2DState(
            initialValue = TestValue.Center,
            anchors = anchors,
            animationSpec = snap(),
        )
        assertEquals(TestValue.Center, state.currentValue)
        assertEquals(Offset(50f, 50f), state.requireOffset())
    }

    @Test
    fun snap_to_updates_value_and_offset() = runTest {
        val state = AnchoredDraggable2DState(
            initialValue = TestValue.Start,
            anchors = anchors,
            animationSpec = snap(),
        )
        state.snapTo(TestValue.End)
        assertEquals(TestValue.End, state.currentValue)
        assertEquals(Offset(100f, 100f), state.requireOffset())
    }

    @Test
    fun saver_saves_and_restores_current_value() {
        val saver = AnchoredDraggable2DState.Saver<TestValue>(
            animationSpec = snap(),
        )
        val state = AnchoredDraggable2DState(
            initialValue = TestValue.Center,
            anchors = anchors,
            animationSpec = snap(),
        )

        val saved = with(saver) { SaverScope { true }.save(state) }
        assertEquals(TestValue.Center, saved)

        val restored = saver.restore(assertNotNull(saved))
        assertEquals(TestValue.Center, restored?.currentValue)
    }

    @Test
    fun target_value_and_closest_value_unspecified_offset() {
        val state = AnchoredDraggable2DState(
            initialValue = TestValue.Center,
            animationSpec = snap(),
        )
        assertEquals(TestValue.Center, state.targetValue)
        assertEquals(TestValue.Center, state.closestValue)
    }

    @Test
    fun dispatch_raw_delta_updates_offset() {
        val state = AnchoredDraggable2DState(
            initialValue = TestValue.Start,
            anchors = anchors,
            animationSpec = snap(),
        )
        val consumed = state.dispatchRawDelta(Offset(20f, 30f))
        assertEquals(Offset(20f, 30f), consumed)
        assertEquals(Offset(20f, 30f), state.requireOffset())
    }

    @Test
    fun update_anchors_updates_state() {
        val state = AnchoredDraggable2DState(
            initialValue = TestValue.Start,
            animationSpec = snap(),
        )
        state.updateAnchors(anchors)
        assertEquals(Offset(0f, 0f), state.requireOffset())
    }
}
