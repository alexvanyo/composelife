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
import com.alexvanyo.composelife.model.CellCoordinate
import com.alexvanyo.composelife.model.MacroCell
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

    @Test
    fun hashlife_subnode_extraction_empty() {
        assertEquals(0, centeredSubnodeLevel3(0L))
        assertEquals(0, oracle.centeredSubnodeLevel3(0L))

        assertEquals(0, centeredHorizontalSubnodeLevel3(0L, 0L))
        assertEquals(0, oracle.centeredHorizontalSubnodeLevel3(0L, 0L))

        assertEquals(0, centeredVerticalSubnodeLevel3(0L, 0L))
        assertEquals(0, oracle.centeredVerticalSubnodeLevel3(0L, 0L))

        assertEquals(0, centeredSubSubnodeLevel4(0L, 0L, 0L, 0L))
        assertEquals(0, oracle.centeredSubSubnodeLevel4(0L, 0L, 0L, 0L))
        assertEquals(0, oracle.centeredSubSubnodeLevel4(MacroCell.Level4Node(0L, 0L, 0L, 0L)))
    }

    @Test
    fun hashlife_subnode_extraction_fuzz() {
        val random = Random(999)
        repeat(500) {
            val a = random.nextLong()
            val b = random.nextLong()
            val c = random.nextLong()
            val d = random.nextLong()

            assertEquals(
                expected = oracle.centeredSubnodeLevel3(a),
                actual = centeredSubnodeLevel3(a),
            )
            assertEquals(
                expected = oracle.centeredHorizontalSubnodeLevel3(a, b),
                actual = centeredHorizontalSubnodeLevel3(a, b),
            )
            assertEquals(
                expected = oracle.centeredVerticalSubnodeLevel3(a, b),
                actual = centeredVerticalSubnodeLevel3(a, b),
            )
            val level4Node = MacroCell.Level4Node(a, b, c, d)
            val expectedLevel4Sub = oracle.centeredSubSubnodeLevel4(level4Node)
            assertEquals(
                expected = expectedLevel4Sub,
                actual = centeredSubSubnodeLevel4(a, b, c, d),
            )
            assertEquals(
                expected = expectedLevel4Sub,
                actual = centeredSubSubnodeLevel4(level4Node),
            )
            assertEquals(
                expected = expectedLevel4Sub,
                actual = oracle.centeredSubSubnodeLevel4(a, b, c, d),
            )
        }
    }

    @Test
    fun hashlife_level4_empty_differential() {
        val emptyNode = MacroCell.Level4Node(0L, 0L, 0L, 0L)
        val kotlinResult = computeLevel4NextGeneration(emptyNode)
        val leanResult = oracle.stepLevel4(emptyNode)
        assertEquals(0L, kotlinResult)
        assertEquals(0L, leanResult)
    }

    @Test
    fun hashlife_level4_fuzz_differential() {
        val random = Random(1337)
        repeat(200) {
            val node = MacroCell.Level4Node(
                nw = random.nextLong(),
                ne = random.nextLong(),
                sw = random.nextLong(),
                se = random.nextLong(),
            )

            val kotlinResult = computeLevel4NextGeneration(node)
            val leanResult = oracle.stepLevel4(node)

            assertEquals(
                expected = leanResult,
                actual = kotlinResult,
                message = "Mismatch for Level 4 next generation",
            )
        }
    }

    @Test
    fun hashlife_level4_canonical_patterns_differential() {
        // Test patterns placed in various positions inside a 16x16 grid
        val patterns = listOf(
            // Still life: Block at (6, 6)
            setOf(
                CellCoordinate(6, 6),
                CellCoordinate(7, 6),
                CellCoordinate(6, 7),
                CellCoordinate(7, 7),
            ),
            // Oscillator: Blinker at (7, 6)..(7, 8)
            setOf(
                CellCoordinate(7, 6),
                CellCoordinate(7, 7),
                CellCoordinate(7, 8),
            ),
            // Still life: Tub at (7, 6)
            setOf(
                CellCoordinate(7, 6),
                CellCoordinate(6, 7),
                CellCoordinate(8, 7),
                CellCoordinate(7, 8),
            ),
            // Glider at (4, 4) moving southeast
            setOf(
                CellCoordinate(5, 4),
                CellCoordinate(6, 5),
                CellCoordinate(4, 6),
                CellCoordinate(5, 6),
                CellCoordinate(6, 6),
            ),
            // Glider centered at boundary of quadrants (7, 7)
            setOf(
                CellCoordinate(8, 7),
                CellCoordinate(9, 8),
                CellCoordinate(7, 9),
                CellCoordinate(8, 9),
                CellCoordinate(9, 9),
            ),
        )

        patterns.forEach(::assertPatternMatchesLevel4AndOracle)
    }

    private fun assertPatternMatchesLevel4AndOracle(pattern: Set<CellCoordinate>) {
        val leaves = coordinatesToLevel4(pattern)

        val kotlinLevel4Result = computeLevel4NextGeneration(leaves)
        val leanLevel4Result = oracle.stepLevel4(leaves)

        assertEquals(
            expected = leanLevel4Result,
            actual = kotlinLevel4Result,
            message = "Kotlin and Lean Level 4 bit results should match for pattern $pattern",
        )

        // Step 1 generation with the formal coordinate-based Conway Game of Life oracle
        val oracleNextGen = oracle.step(pattern, 1)

        // Filter ground truth oracle results to the central 8x8 window [4, 11] x [4, 11]
        val expectedCenterWindow = oracleNextGen.filter { (x, y) ->
            x in 4..11 && y in 4..11
        }.toSet()

        // Convert Level 4 stepped 8x8 leaf back to coordinates at offset (4, 4)
        val actualCenterCoords = leafToCoordinates(kotlinLevel4Result, offsetX = 4, offsetY = 4)

        assertEquals(
            expected = expectedCenterWindow,
            actual = actualCenterCoords,
            message = "Level 4 result coordinates must match formal Conway GoL ground truth for pattern $pattern",
        )
    }
}
