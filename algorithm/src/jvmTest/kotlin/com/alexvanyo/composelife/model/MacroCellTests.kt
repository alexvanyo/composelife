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

class MacroCellTests {

    @Test
    fun alive_cell_is_correct() {
        val cell = MacroCell.Cell.AliveCell

        assertEquals(0, cell.level)
        assertTrue(cell.isAlive)
        assertEquals(1, cell.size)
    }

    @Test
    fun dead_cell_is_correct() {
        val cell = MacroCell.Cell.DeadCell

        assertEquals(0, cell.level)
        assertFalse(cell.isAlive)
        assertEquals(0, cell.size)
    }

    @Test
    fun making_dead_cell_alive_is_correct() {
        assertEquals(
            MacroCell.Cell.AliveCell,
            MacroCell.Cell.DeadCell.withCell(IntOffset.Zero, true),
        )
    }

    @Test
    fun making_alive_cell_dead_is_correct() {
        assertEquals(
            MacroCell.Cell.DeadCell,
            MacroCell.Cell.AliveCell.withCell(IntOffset.Zero, false),
        )
    }

    @Test
    fun making_specific_cell_alive_is_correct() {
        assertEquals(
            MacroCell.CellNode(
                createEmptyMacroCell(3),
                MacroCell.CellNode(
                    createEmptyMacroCell(2),
                    createEmptyMacroCell(2),
                    MacroCell.CellNode(
                        MacroCell.CellNode(
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.AliveCell,
                        ),
                        createEmptyMacroCell(1),
                        createEmptyMacroCell(1),
                        createEmptyMacroCell(1),
                    ),
                    createEmptyMacroCell(2),
                ),
                createEmptyMacroCell(3),
                createEmptyMacroCell(3),
            ),
            createEmptyMacroCell(4).withCell(IntOffset(9, 5), true),
        )
    }

    @Test
    fun create_empty_macro_cell_at_negative_level_throws() {
        assertFailsWith<IllegalArgumentException> {
            createEmptyMacroCell(-1)
        }
    }

    @Test
    fun create_empty_macro_cell_at_level_0_is_correct() {
        assertEquals(
            MacroCell.Cell.DeadCell,
            createEmptyMacroCell(0),
        )
    }

    @Test
    fun create_empty_macro_cell_at_level_1_is_correct() {
        assertEquals(
            MacroCell.CellNode(
                MacroCell.Cell.DeadCell,
                MacroCell.Cell.DeadCell,
                MacroCell.Cell.DeadCell,
                MacroCell.Cell.DeadCell,
            ),
            createEmptyMacroCell(1),
        )
    }

    @Test
    fun create_empty_macro_cell_at_level_2_is_correct() {
        assertEquals(
            MacroCell.CellNode(
                MacroCell.CellNode(
                    MacroCell.Cell.DeadCell,
                    MacroCell.Cell.DeadCell,
                    MacroCell.Cell.DeadCell,
                    MacroCell.Cell.DeadCell,
                ),
                MacroCell.CellNode(
                    MacroCell.Cell.DeadCell,
                    MacroCell.Cell.DeadCell,
                    MacroCell.Cell.DeadCell,
                    MacroCell.Cell.DeadCell,
                ),
                MacroCell.CellNode(
                    MacroCell.Cell.DeadCell,
                    MacroCell.Cell.DeadCell,
                    MacroCell.Cell.DeadCell,
                    MacroCell.Cell.DeadCell,
                ),
                MacroCell.CellNode(
                    MacroCell.Cell.DeadCell,
                    MacroCell.Cell.DeadCell,
                    MacroCell.Cell.DeadCell,
                    MacroCell.Cell.DeadCell,
                ),
            ),
            createEmptyMacroCell(2),
        )
    }

    @Test
    fun create_empty_macro_cell_at_level_3_is_correct() {
        assertEquals(
            MacroCell.CellNode(
                MacroCell.CellNode(
                    MacroCell.CellNode(
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                    ),
                    MacroCell.CellNode(
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                    ),
                    MacroCell.CellNode(
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                    ),
                    MacroCell.CellNode(
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                    ),
                ),
                MacroCell.CellNode(
                    MacroCell.CellNode(
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                    ),
                    MacroCell.CellNode(
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                    ),
                    MacroCell.CellNode(
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                    ),
                    MacroCell.CellNode(
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                    ),
                ),
                MacroCell.CellNode(
                    MacroCell.CellNode(
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                    ),
                    MacroCell.CellNode(
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                    ),
                    MacroCell.CellNode(
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                    ),
                    MacroCell.CellNode(
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                    ),
                ),
                MacroCell.CellNode(
                    MacroCell.CellNode(
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                    ),
                    MacroCell.CellNode(
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                    ),
                    MacroCell.CellNode(
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                    ),
                    MacroCell.CellNode(
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                    ),
                ),
            ),
            createEmptyMacroCell(3),
        )
    }

    @Test
    fun checking_contains_specific_cell_is_correct() {
        assertTrue(
            MacroCell.CellNode(
                createEmptyMacroCell(3),
                MacroCell.CellNode(
                    createEmptyMacroCell(2),
                    createEmptyMacroCell(2),
                    MacroCell.CellNode(
                        MacroCell.CellNode(
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.AliveCell,
                        ),
                        createEmptyMacroCell(1),
                        createEmptyMacroCell(1),
                        createEmptyMacroCell(1),
                    ),
                    createEmptyMacroCell(2),
                ),
                createEmptyMacroCell(3),
                createEmptyMacroCell(3),
            ).contains(IntOffset(9, 5)),
        )
    }

    @Test
    fun checking_does_not_contain_specific_cell_is_correct() {
        assertFalse(
            MacroCell.CellNode(
                createEmptyMacroCell(3),
                MacroCell.CellNode(
                    createEmptyMacroCell(2),
                    createEmptyMacroCell(2),
                    MacroCell.CellNode(
                        MacroCell.CellNode(
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.AliveCell,
                        ),
                        createEmptyMacroCell(1),
                        createEmptyMacroCell(1),
                        createEmptyMacroCell(1),
                    ),
                    createEmptyMacroCell(2),
                ),
                createEmptyMacroCell(3),
                createEmptyMacroCell(3),
            ).contains(IntOffset(9, 6)),
        )
    }

    @Test
    fun checking_does_not_contain_outside_range_cell_is_correct() {
        assertFalse(
            MacroCell.CellNode(
                createEmptyMacroCell(3),
                MacroCell.CellNode(
                    createEmptyMacroCell(2),
                    createEmptyMacroCell(2),
                    MacroCell.CellNode(
                        MacroCell.CellNode(
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.AliveCell,
                        ),
                        createEmptyMacroCell(1),
                        createEmptyMacroCell(1),
                        createEmptyMacroCell(1),
                    ),
                    createEmptyMacroCell(2),
                ),
                createEmptyMacroCell(3),
                createEmptyMacroCell(3),
            ).contains(IntOffset(-2, -2)),
        )
    }
}
