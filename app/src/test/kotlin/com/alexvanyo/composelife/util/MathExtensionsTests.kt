package com.alexvanyo.composelife.util

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Nested
import org.junit.jupiter.api.Test

class MathExtensionsTests {

    @Nested
    inner class CeilToOddTests {
        @Test
        fun `-1 goes to itself`() {
            assertEquals(-1, (-1).ceilToOdd())
        }

        @Test
        fun `0 goes to 1`() {
            assertEquals(1, 0.ceilToOdd())
        }

        @Test
        fun `1 goes to itself`() {
            assertEquals(1, 1.ceilToOdd())
        }

        @Test
        fun `12 goes to 13`() {
            assertEquals(13, 12.ceilToOdd())
        }
    }
}
