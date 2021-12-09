package com.alexvanyo.composelife.util

import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Nested
import org.junit.jupiter.api.Test

class BoundsExtensionsTests {

    @Nested
    inner class ContainedPointsTests {

        @Test
        fun `empty IntRect returns single point`() {
            assertEquals(
                listOf(IntOffset(2, 2)),
                IntRect(IntOffset(2, 2), 0).containedPoints()
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
                    IntOffset(4, 13)
                ),
                IntRect(
                    IntOffset(2, 11),
                    IntOffset(4, 13)
                ).containedPoints()
            )
        }
    }

    @Nested
    inner class PairToIntOffsetTests {

        @Test
        fun `pair to int offset is correct`() {
            assertEquals(
                IntOffset(11, 13),
                (11 to 13).toIntOffset()
            )
        }
    }

    @Nested
    inner class IntOffsetToPairTests {

        @Test
        fun `pair to int offset is correct`() {
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
                    IntOffset(-2, -5)
                ),
                IntOffset(-3, -6).getNeighbors()
            )
        }
    }

    @Nested
    inner class FloorOffsetTests {

        @Test
        fun `floor positive offset is correct`() {
            assertEquals(
                IntOffset(7, 9),
                floor(Offset(7.2f, 9.9f))
            )
        }

        @Test
        fun `floor negative offset is correct`() {
            assertEquals(
                IntOffset(-20, -7),
                floor(Offset(-19.3f, -6.8f))
            )
        }
    }
}
