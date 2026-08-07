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
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertNotEquals
import kotlin.test.assertNull
import kotlin.test.assertTrue

class MapDraggableAnchors2DTests {

    enum class TestAnchor {
        A,
        B,
        C,
    }

    @Test
    fun position_of_known_anchor_returns_offset() {
        val anchors = DraggableAnchors2D {
            TestAnchor.A at Offset(0f, 0f)
            TestAnchor.B at Offset(100f, 200f)
        }
        assertEquals(Offset(0f, 0f), anchors.positionOf(TestAnchor.A))
        assertEquals(Offset(100f, 200f), anchors.positionOf(TestAnchor.B))
    }

    @Test
    fun position_of_unknown_anchor_returns_unspecified() {
        val anchors = DraggableAnchors2D {
            TestAnchor.A at Offset(0f, 0f)
        }
        assertEquals(Offset.Unspecified, anchors.positionOf(TestAnchor.B))
    }

    @Test
    fun has_position_for_returns_correct_boolean() {
        val anchors = DraggableAnchors2D {
            TestAnchor.A at Offset(0f, 0f)
        }
        assertTrue(anchors.hasPositionFor(TestAnchor.A))
        assertFalse(anchors.hasPositionFor(TestAnchor.B))
    }

    @Test
    fun closest_anchor_returns_null_when_empty() {
        val anchors = DraggableAnchors2D<TestAnchor> {}
        assertNull(anchors.closestAnchor(Offset(50f, 50f)))
    }

    @Test
    fun closest_anchor_returns_closest_by_distance() {
        val anchors = DraggableAnchors2D {
            TestAnchor.A at Offset(0f, 0f)
            TestAnchor.B at Offset(100f, 0f)
            TestAnchor.C at Offset(0f, 100f)
        }
        assertEquals(TestAnchor.A, anchors.closestAnchor(Offset(10f, 10f)))
        assertEquals(TestAnchor.B, anchors.closestAnchor(Offset(90f, 5f)))
        assertEquals(TestAnchor.C, anchors.closestAnchor(Offset(5f, 95f)))
    }

    @Test
    fun size_returns_correct_count() {
        val emptyAnchors = DraggableAnchors2D<TestAnchor> {}
        assertEquals(0, emptyAnchors.size)

        val nonEmpytAnchors = DraggableAnchors2D {
            TestAnchor.A at Offset(0f, 0f)
            TestAnchor.B at Offset(10f, 10f)
        }
        assertEquals(2, nonEmpytAnchors.size)
    }

    @Test
    fun equals_and_hash_code_work_correctly() {
        val anchors1 = DraggableAnchors2D {
            TestAnchor.A at Offset(0f, 0f)
            TestAnchor.B at Offset(10f, 10f)
        }
        val anchors2 = DraggableAnchors2D {
            TestAnchor.A at Offset(0f, 0f)
            TestAnchor.B at Offset(10f, 10f)
        }
        val anchors3 = DraggableAnchors2D {
            TestAnchor.A at Offset(0f, 0f)
        }

        assertEquals(anchors1, anchors1)
        assertEquals(anchors1, anchors2)
        assertEquals(anchors1.hashCode(), anchors2.hashCode())

        assertNotEquals(anchors1, anchors3)
        assertFalse(anchors1.equals("NotDraggableAnchors"))
    }

    @Test
    fun to_string_returns_formatted_string() {
        val anchors = DraggableAnchors2D {
            TestAnchor.A at Offset(0f, 0f)
        }
        assertTrue(anchors.toString().startsWith("MapDraggableAnchors2D("))
    }
}
