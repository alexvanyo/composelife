/*
 * Copyright 2022 The Android Open Source Project
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

package com.alexvanyo.composelife.util

import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.geometry.Rect
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import org.junit.jupiter.api.Nested
import org.junit.jupiter.api.Test
import kotlin.test.assertEquals

class BoundsExtensionsTests {

    @Nested
    inner class ContainedPointsTests {

        @Test
        fun `empty IntRect returns single point`() {
            assertEquals(
                listOf(IntOffset(2, 2)),
                IntRect(IntOffset(2, 2), 0).containedPoints(),
            )
        }

        @Test
        fun `non-empty IntRect returns correct order`() {
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

    @Nested
    inner class PairToIntOffsetTests {

        @Test
        fun `pair to int offset is correct`() {
            assertEquals(
                IntOffset(11, 13),
                (11 to 13).toIntOffset(),
            )
        }
    }

    @Nested
    inner class IntOffsetToPairTests {

        @Test
        fun `int offset to pair is correct`() {
            assertEquals(
                11 to 13,
                IntOffset(11, 13).toPair(),
            )
        }
    }

    @Nested
    inner class GetNeighborsTests {

        @Test
        fun `neighbors are correct`() {
            assertEquals(
                setOf(
                    IntOffset(-4, -7),
                    IntOffset(-3, -7),
                    IntOffset(-2, -7),
                    IntOffset(-4, -6),
                    IntOffset(-2, -6),
                    IntOffset(-4, -5),
                    IntOffset(-3, -5),
                    IntOffset(-2, -5),
                ),
                IntOffset(-3, -6).getNeighbors(),
            )
        }
    }

    @Nested
    inner class FloorOffsetTests {

        @Test
        fun `floor positive offset is correct`() {
            assertEquals(
                IntOffset(7, 9),
                floor(Offset(7.2f, 9.9f)),
            )
        }

        @Test
        fun `floor negative offset is correct`() {
            assertEquals(
                IntOffset(-20, -7),
                floor(Offset(-19.3f, -6.8f)),
            )
        }
    }

    @Nested
    inner class IntRectToRectTests {

        @Test
        fun `int rect to rect is correct`() {
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
    }

    @Nested
    inner class RingIndexTests {

        @Test
        fun `0`() {
            assertEquals(0, IntOffset(0, 0).toRingIndex())
        }

        @Test
        fun `1`() {
            assertEquals(1, IntOffset(-1, -1).toRingIndex())
        }

        @Test
        fun `2`() {
            assertEquals(2, IntOffset(0, -1).toRingIndex())
        }

        @Test
        fun `3`() {
            assertEquals(3, IntOffset(1, -1).toRingIndex())
        }

        @Test
        fun `4`() {
            assertEquals(4, IntOffset(1, 0).toRingIndex())
        }

        @Test
        fun `5`() {
            assertEquals(5, IntOffset(1, 1).toRingIndex())
        }

        @Test
        fun `6`() {
            assertEquals(6, IntOffset(0, 1).toRingIndex())
        }

        @Test
        fun `7`() {
            assertEquals(7, IntOffset(-1, 1).toRingIndex())
        }

        @Test
        fun `8`() {
            assertEquals(8, IntOffset(-1, 0).toRingIndex())
        }

        @Test
        fun `9`() {
            assertEquals(9, IntOffset(-2, -2).toRingIndex())
        }
    }

    @Nested
    inner class RingOffsetTests {

        @Test
        fun `0`() {
            assertEquals(IntOffset(0, 0), 0.toRingOffset())
        }

        @Test
        fun `1`() {
            assertEquals(IntOffset(-1, -1), 1.toRingOffset())
        }

        @Test
        fun `2`() {
            assertEquals(IntOffset(0, -1), 2.toRingOffset())
        }

        @Test
        fun `3`() {
            assertEquals(IntOffset(1, -1), 3.toRingOffset())
        }

        @Test
        fun `4`() {
            assertEquals(IntOffset(1, 0), 4.toRingOffset())
        }

        @Test
        fun `5`() {
            assertEquals(IntOffset(1, 1), 5.toRingOffset())
        }

        @Test
        fun `6`() {
            assertEquals(IntOffset(0, 1), 6.toRingOffset())
        }

        @Test
        fun `7`() {
            assertEquals(IntOffset(-1, 1), 7.toRingOffset())
        }

        @Test
        fun `8`() {
            assertEquals(IntOffset(-1, 0), 8.toRingOffset())
        }

        @Test
        fun `9`() {
            assertEquals(IntOffset(-2, -2), 9.toRingOffset())
        }
    }
}
