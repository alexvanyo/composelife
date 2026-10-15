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

package com.alexvanyo.composelife.model

import androidx.compose.ui.unit.IntOffset
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.test.assertFalse
import kotlin.test.assertTrue

@Suppress("TooManyFunctions")
class MacroCellTests {
    @Test
    fun making_specific_cell_alive_is_correct() {
        assertEquals(
            MacroCell.CellNode(
                createEmptyMacroCell(4),
                MacroCell.Level4Node(
                    0uL,
                    0uL,
                    LeafNode(setOf(IntOffset(3, 7))),
                    0uL,
                ),
                createEmptyMacroCell(4),
                createEmptyMacroCell(4),
            ),
            createEmptyMacroCell(5).withCell(IntOffset(19, 15), true),
        )
    }

    @Test
    fun create_empty_macro_cell_at_negative_level_throws() {
        assertFailsWith<IllegalArgumentException> {
            createEmptyMacroCell(-1)
        }
    }

    @Test
    fun create_empty_macro_cell_at_level_0_throws() {
        assertFailsWith<IllegalArgumentException> {
            createEmptyMacroCell(0)
        }
    }

    @Test
    fun create_empty_macro_cell_at_level_1_throws() {
        assertFailsWith<IllegalArgumentException> {
            createEmptyMacroCell(1)
        }
    }

    @Test
    fun create_empty_macro_cell_at_level_2_throws() {
        assertFailsWith<IllegalArgumentException> {
            createEmptyMacroCell(2)
        }
    }

    @Test
    fun create_empty_macro_cell_at_level_3_throws() {
        assertFailsWith<IllegalArgumentException> {
            createEmptyMacroCell(3)
        }
    }

    @Test
    fun create_empty_macro_cell_at_level_4_is_correct() {
        assertEquals(
            MacroCell.Level4Node(
                0uL,
                0uL,
                0uL,
                0uL,
            ),
            createEmptyMacroCell(4),
        )
    }

    @Test
    fun create_empty_macro_cell_at_level_5_is_correct() {
        assertEquals(
            MacroCell.CellNode(
                MacroCell.Level4Node(
                    0uL,
                    0uL,
                    0uL,
                    0uL,
                ),
                MacroCell.Level4Node(
                    0uL,
                    0uL,
                    0uL,
                    0uL,
                ),
                MacroCell.Level4Node(
                    0uL,
                    0uL,
                    0uL,
                    0uL,
                ),
                MacroCell.Level4Node(
                    0uL,
                    0uL,
                    0uL,
                    0uL,
                ),
            ),
            createEmptyMacroCell(5),
        )
    }

    @Test
    fun checking_contains_specific_cell_is_correct() {
        assertTrue(
            MacroCell
                .CellNode(
                    createEmptyMacroCell(4),
                    MacroCell.Level4Node(
                        0uL,
                        0uL,
                        LeafNode(setOf(IntOffset(3, 7))),
                        0uL,
                    ),
                    createEmptyMacroCell(4),
                    createEmptyMacroCell(4),
                ).contains(IntOffset(19, 15)),
        )
    }

    @Test
    fun checking_does_not_contain_specific_cell_is_correct() {
        assertFalse(
            MacroCell
                .CellNode(
                    createEmptyMacroCell(4),
                    MacroCell.Level4Node(
                        0uL,
                        0uL,
                        LeafNode(setOf(IntOffset(3, 7))),
                        0uL,
                    ),
                    createEmptyMacroCell(4),
                    createEmptyMacroCell(4),
                ).contains(IntOffset(19, 16)),
        )
    }

    @Test
    fun checking_does_not_contain_outside_range_cell_is_correct() {
        assertFalse(
            MacroCell
                .CellNode(
                    createEmptyMacroCell(4),
                    MacroCell.Level4Node(
                        0uL,
                        0uL,
                        LeafNode(setOf(IntOffset(3, 7))),
                        0uL,
                    ),
                    createEmptyMacroCell(4),
                    createEmptyMacroCell(4),
                ).contains(IntOffset(-2, -2)),
        )
    }

    @Test
    fun toMask_is_correct() {
        repeat(64) { bit ->
            assertEquals(
                1uL shl bit,
                intOffsetFromBit(bit).toMask(),
            )
        }
    }

    @Test
    fun making_cells_alive_and_dead_in_all_quadrants_is_correct() {
        val emptyCell = createEmptyMacroCell(5)
        // NW quadrant (x=2, y=2)
        val nwCell = emptyCell.withCell(IntOffset(2, 2), true)
        assertTrue(nwCell.contains(IntOffset(2, 2)))
        val nwCleared = nwCell.withCell(IntOffset(2, 2), false)
        assertFalse(nwCleared.contains(IntOffset(2, 2)))

        // NE quadrant (x=18, y=2)
        val neCell = emptyCell.withCell(IntOffset(18, 2), true)
        assertTrue(neCell.contains(IntOffset(18, 2)))
        val neCleared = neCell.withCell(IntOffset(18, 2), false)
        assertFalse(neCleared.contains(IntOffset(18, 2)))

        // SW quadrant (x=2, y=18)
        val swCell = emptyCell.withCell(IntOffset(2, 18), true)
        assertTrue(swCell.contains(IntOffset(2, 18)))
        val swCleared = swCell.withCell(IntOffset(2, 18), false)
        assertFalse(swCleared.contains(IntOffset(2, 18)))

        // SE quadrant (x=18, y=18)
        val seCell = emptyCell.withCell(IntOffset(18, 18), true)
        assertTrue(seCell.contains(IntOffset(18, 18)))
        val seCleared = seCell.withCell(IntOffset(18, 18), false)
        assertFalse(seCleared.contains(IntOffset(18, 18)))
    }

    @Test
    fun making_cells_alive_and_dead_in_level_4_node_is_correct() {
        val emptyLevel4 = createEmptyMacroCell(4)
        // NW (0,0)
        val nw = emptyLevel4.withCell(IntOffset(0, 0), true)
        assertTrue(nw.contains(IntOffset(0, 0)))
        assertFalse(nw.withCell(IntOffset(0, 0), false).contains(IntOffset(0, 0)))

        // NE (8,0)
        val ne = emptyLevel4.withCell(IntOffset(8, 0), true)
        assertTrue(ne.contains(IntOffset(8, 0)))
        assertFalse(ne.withCell(IntOffset(8, 0), false).contains(IntOffset(8, 0)))

        // SW (0,8)
        val sw = emptyLevel4.withCell(IntOffset(0, 8), true)
        assertTrue(sw.contains(IntOffset(0, 8)))
        assertFalse(sw.withCell(IntOffset(0, 8), false).contains(IntOffset(0, 8)))

        // SE (8,8)
        val se = emptyLevel4.withCell(IntOffset(8, 8), true)
        assertTrue(se.contains(IntOffset(8, 8)))
        assertFalse(se.withCell(IntOffset(8, 8), false).contains(IntOffset(8, 8)))
    }

    @Test
    fun withCell_out_of_bounds_throws() {
        val cell = createEmptyMacroCell(4)
        assertFailsWith<IllegalArgumentException> {
            cell.withCell(IntOffset(-1, 0), true)
        }
        assertFailsWith<IllegalArgumentException> {
            cell.withCell(IntOffset(16, 0), true)
        }
    }

    @Test
    fun minimumMacroCellLevel_is_correct() {
        assertEquals(4u, f_Algorithm_minimumMacroCellLevel(0u))
        assertEquals(4u, f_Algorithm_minimumMacroCellLevel(1u))
        assertEquals(4u, f_Algorithm_minimumMacroCellLevel(16u))
        assertEquals(5u, f_Algorithm_minimumMacroCellLevel(17u))
        assertEquals(5u, f_Algorithm_minimumMacroCellLevel(32u))
        assertEquals(6u, f_Algorithm_minimumMacroCellLevel(33u))
    }

    @Test
    fun canonicalCellNodeEquals_is_correct() {
        val empty4 = createEmptyMacroCell(4)
        val empty5A = createEmptyMacroCell(5)
        val empty5B = MacroCell.CellNode(empty4, empty4, empty4, empty4)

        assertTrue(f_Algorithm_canonicalCellNodeEquals(empty5A, empty5B))
        assertFalse(f_Algorithm_canonicalCellNodeEquals(empty4, empty4))

        val nonZeroCell = empty4.withCell(IntOffset(0, 0), true)
        val cellWithDiff = MacroCell.CellNode(nonZeroCell, empty4, empty4, empty4)
        assertFalse(f_Algorithm_canonicalCellNodeEquals(empty5A, cellWithDiff))
    }

    @Test
    fun canonicalizeMacroCellWith_level4_calls_internLevel4() {
        val level4 = createEmptyMacroCell(4)
        var called = false
        val result = f_Algorithm_canonicalizeMacroCellWith(
            m = level4,
            internLevel4 = {
                called = true
                it
            },
            findExistingCell = { null },
            canonicalizeSubnode = { it },
            internCell = { it },
        )
        assertTrue(called)
        assertEquals(level4, result)
    }

    @Test
    fun canonicalizeMacroCellWith_hit_returns_existing() {
        val cell = createEmptyMacroCell(5)
        val existing = createEmptyMacroCell(5)
        val result = f_Algorithm_canonicalizeMacroCellWith(
            m = cell,
            internLevel4 = { it },
            findExistingCell = { existing },
            canonicalizeSubnode = { it },
            internCell = { it },
        )
        assertEquals(existing, result)
    }

    @Test
    fun canonicalizeMacroCellWith_miss_zero_calls_canonicalize_once() {
        val cell = createEmptyMacroCell(5)
        var subnodeCallCount = 0
        val result = f_Algorithm_canonicalizeMacroCellWith(
            m = cell,
            internLevel4 = { it },
            findExistingCell = { null },
            canonicalizeSubnode = {
                subnodeCallCount++
                it
            },
            internCell = { it },
        )
        assertEquals(1, subnodeCallCount)
        assertEquals(cell, result)
    }

    @Test
    fun canonicalizeMacroCellWith_miss_nonzero_calls_canonicalize_four_times() {
        val cell = createEmptyMacroCell(5).withCell(IntOffset(0, 0), true)
        var subnodeCallCount = 0
        val result = f_Algorithm_canonicalizeMacroCellWith(
            m = cell,
            internLevel4 = { it },
            findExistingCell = { null },
            canonicalizeSubnode = {
                subnodeCallCount++
                it
            },
            internCell = { it },
        )
        assertEquals(4, subnodeCallCount)
        assertEquals(cell, result)
    }

    @Test
    fun computeGenerationStep_computes_steps_and_thresholds() {
        val cell = createEmptyMacroCell(4)
        val initial = HashLifeStepState(
            offsetX = 10,
            offsetY = 20,
            macroCell = cell,
        )
        var stepCalls = 0
        val res = f_Algorithm_computeGenerationStep(
            step = 3u,
            st = initial,
            computedGenerations = 10uL,
            macroKeep = 4u,
            leafKeep = 8u,
            stepOneGen = {
                stepCalls++
                it
            },
        )
        assertEquals(3, stepCalls)
        assertEquals(initial.offsetX, res.finalState.offsetX)
        assertEquals(initial.offsetY, res.finalState.offsetY)
        assertEquals(initial.macroCell, res.finalState.macroCell)
        // 10 + 3 = 13. oldestMacro = max(0, 13 - 4) = 9. oldestLeaf = max(0, 13 - 8) = 5.
        assertEquals(9uL, res.thresholds.oldestMacroToKeep)
        assertEquals(5uL, res.thresholds.oldestLeafToKeep)
    }
}
