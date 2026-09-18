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
import kotlin.random.Random
import kotlin.test.Test
import kotlin.test.assertEquals

class GameOfLifeLeanConformanceTests {

    private val oracle = LeanGameOfLifeOracle()

    @Test
    fun empty_grid_stability() {
        val empty = emptySet<CellCoordinate>()
        assertEquals(empty, stepGenerations(empty, 0))
        assertEquals(empty, stepGenerations(empty, 1))
        assertEquals(empty, stepGenerations(empty, 5))
        assertEquals(empty, oracle.step(empty, 1))
        assertEquals(empty, oracle.step(empty, 5))
    }

    @Test
    fun block_still_life() {
        val block = setOf(
            CellCoordinate(0, 0),
            CellCoordinate(0, 1),
            CellCoordinate(1, 0),
            CellCoordinate(1, 1),
        )
        val kotlinNext = stepGenerations(block, 1)
        val oracleNext = oracle.step(block, 1)

        assertEquals(block, kotlinNext)
        assertEquals(block, oracleNext)
    }

    @Test
    fun tub_still_life() {
        val tub = setOf(
            CellCoordinate(1, 0),
            CellCoordinate(0, 1),
            CellCoordinate(2, 1),
            CellCoordinate(1, 2),
        )
        val kotlinNext = stepGenerations(tub, 1)
        val oracleNext = oracle.step(tub, 1)

        assertEquals(tub, kotlinNext)
        assertEquals(tub, oracleNext)
    }

    @Test
    fun blinker_oscillator() {
        val blinkerH = setOf(
            CellCoordinate(0, 1),
            CellCoordinate(1, 1),
            CellCoordinate(2, 1),
        )
        val blinkerV = setOf(
            CellCoordinate(1, 0),
            CellCoordinate(1, 1),
            CellCoordinate(1, 2),
        )

        val kotlinStep1 = stepGenerations(blinkerH, 1)
        val oracleStep1 = oracle.step(blinkerH, 1)
        assertEquals(blinkerV, kotlinStep1)
        assertEquals(blinkerV, oracleStep1)

        val kotlinStep2 = stepGenerations(blinkerH, 2)
        val oracleStep2 = oracle.step(blinkerH, 2)
        assertEquals(blinkerH, kotlinStep2)
        assertEquals(blinkerH, oracleStep2)
    }

    @Test
    fun toad_oscillator() {
        val toad = setOf(
            CellCoordinate(1, 1),
            CellCoordinate(2, 1),
            CellCoordinate(3, 1),
            CellCoordinate(0, 2),
            CellCoordinate(1, 2),
            CellCoordinate(2, 2),
        )

        val kotlinStep2 = stepGenerations(toad, 2)
        val oracleStep2 = oracle.step(toad, 2)
        assertEquals(toad, kotlinStep2)
        assertEquals(toad, oracleStep2)
    }

    @Test
    fun glider_period_four_shift() {
        val glider = setOf(
            CellCoordinate(1, 0),
            CellCoordinate(2, 1),
            CellCoordinate(0, 2),
            CellCoordinate(1, 2),
            CellCoordinate(2, 2),
        )
        val shiftedGlider = setOf(
            CellCoordinate(2, 1),
            CellCoordinate(3, 2),
            CellCoordinate(1, 3),
            CellCoordinate(2, 3),
            CellCoordinate(3, 3),
        )

        val kotlinStep4 = stepGenerations(glider, 4)
        val oracleStep4 = oracle.step(glider, 4)

        assertEquals(shiftedGlider, kotlinStep4)
        assertEquals(shiftedGlider, oracleStep4)
    }

    @Test
    fun translation_symmetry_commutes() {
        val glider = setOf(
            CellCoordinate(1, 0),
            CellCoordinate(2, 1),
            CellCoordinate(0, 2),
            CellCoordinate(1, 2),
            CellCoordinate(2, 2),
        )
        val offsetGlider = glider.map { CellCoordinate(it.x + 157, it.y + 72) }.toSet()

        val stepped = stepGenerations(offsetGlider, 2)
        val oracleStepped = oracle.step(offsetGlider, 2)

        assertEquals(stepped, oracleStepped)
    }

    @Test
    fun differential_fuzz_conformance() {
        val random = Random(42)
        repeat(10) {
            val cellCount = random.nextInt(5, 25)
            val seed = buildSet(cellCount) {
                while (size < cellCount) {
                    add(CellCoordinate(random.nextInt(-10, 10), random.nextInt(-10, 10)))
                }
            }

            for (step in 1..4) {
                val kotlinResult = stepGenerations(seed, step)
                val oracleResult = oracle.step(seed, step)
                assertEquals(
                    expected = kotlinResult,
                    actual = oracleResult,
                    message = "Mismatch at step $step for seed: $seed",
                )
            }
        }
    }

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
}
