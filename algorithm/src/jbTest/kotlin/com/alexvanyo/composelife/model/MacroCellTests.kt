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
                    0L,
                    0L,
                    LeafNode(setOf(IntOffset(3, 7))),
                    0L,
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
                0L,
                0L,
                0L,
                0L,
            ),
            createEmptyMacroCell(4),
        )
    }

    @Test
    fun create_empty_macro_cell_at_level_5_is_correct() {
        assertEquals(
            MacroCell.CellNode(
                MacroCell.Level4Node(
                    0L,
                    0L,
                    0L,
                    0L,
                ),
                MacroCell.Level4Node(
                    0L,
                    0L,
                    0L,
                    0L,
                ),
                MacroCell.Level4Node(
                    0L,
                    0L,
                    0L,
                    0L,
                ),
                MacroCell.Level4Node(
                    0L,
                    0L,
                    0L,
                    0L,
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
                        0L,
                        0L,
                        LeafNode(setOf(IntOffset(3, 7))),
                        0L,
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
                        0L,
                        0L,
                        LeafNode(setOf(IntOffset(3, 7))),
                        0L,
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
                        0L,
                        0L,
                        LeafNode(setOf(IntOffset(3, 7))),
                        0L,
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
                1L shl bit,
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
}
