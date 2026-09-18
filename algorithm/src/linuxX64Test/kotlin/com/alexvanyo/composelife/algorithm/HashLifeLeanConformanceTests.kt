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

package com.alexvanyo.composelife.algorithm

import com.alexvanyo.composelife.algorithm.lean.LeanGameOfLifeOracle
import kotlin.random.Random
import kotlin.test.Test
import kotlin.test.assertEquals

class HashLifeLeanConformanceTests {

    private val oracle = LeanGameOfLifeOracle()

    @Test
    fun hashlife_4x4_bit_computation_exhaustive_differential() {
        for (bits in 0..0xFFFF) {
            val kotlinResult = bits.computeNextGeneration()
            val leanResult = oracle.step4x4Bits(bits)
            assertEquals(
                expected = leanResult,
                actual = kotlinResult,
                message = "Mismatch for 4x4 bit pattern 0x${bits.toString(16)}",
            )
        }
    }

    @Test
    fun hashlife_leaf_empty_differential() {
        val kotlinResult = 0L.computeLeafNextGeneration()
        val leanResult = oracle.stepLeafBits(0L)
        assertEquals(0, kotlinResult)
        assertEquals(0, leanResult)
    }

    @Test
    fun hashlife_leaf_canonical_patterns_differential() {
        val block = (1L shl 0x0F) or (1L shl 0x1A) or (1L shl 0x25) or (1L shl 0x30)
        assertEquals(
            expected = oracle.stepLeafBits(block),
            actual = block.computeLeafNextGeneration(),
        )

        val blinker = (1L shl 0x0E) or (1L shl 0x0F) or (1L shl 0x1A)
        assertEquals(
            expected = oracle.stepLeafBits(blinker),
            actual = blinker.computeLeafNextGeneration(),
        )

        val tub = (1L shl 0x0D) or (1L shl 0x0E) or (1L shl 0x1A) or (1L shl 0x25)
        assertEquals(
            expected = oracle.stepLeafBits(tub),
            actual = tub.computeLeafNextGeneration(),
        )
    }

    @Test
    fun hashlife_leaf_fuzz_differential() {
        val random = Random(42)
        repeat(1000) {
            val bits = random.nextLong()
            val kotlinResult = bits.computeLeafNextGeneration()
            val leanResult = oracle.stepLeafBits(bits)
            assertEquals(
                expected = leanResult,
                actual = kotlinResult,
                message = "Mismatch for 8x8 leaf bit pattern 0x${bits.toString(16)}",
            )
        }
    }
}
