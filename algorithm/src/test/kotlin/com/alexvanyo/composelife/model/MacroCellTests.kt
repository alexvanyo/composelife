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
import org.junit.jupiter.api.Nested
import org.junit.jupiter.api.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class MacroCellTests {

    @Test
    fun `alive cell is correct`() {
        val cell = MacroCell.Cell.AliveCell

        assertEquals(0, cell.level)
        assertTrue(cell.isAlive)
        assertEquals(1, cell.size)
    }

    @Test
    fun `dead cell is correct`() {
        val cell = MacroCell.Cell.DeadCell

        assertEquals(0, cell.level)
        assertFalse(cell.isAlive)
        assertEquals(0, cell.size)
    }

    @Nested
    inner class WithCellTests {

        @Test
        fun `making dead cell alive is correct`() {
            assertEquals(
                MacroCell.Cell.AliveCell,
                MacroCell.Cell.DeadCell.withCell(IntOffset.Zero, true)
            )
        }

        @Test
        fun `making alive cell dead is correct`() {
            assertEquals(
                MacroCell.Cell.DeadCell,
                MacroCell.Cell.AliveCell.withCell(IntOffset.Zero, false)
            )
        }

        @Test
        fun `making specific cell alive is correct`() {
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
                                MacroCell.Cell.AliveCell
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
                createEmptyMacroCell(4).withCell(IntOffset(9, 5), true)
            )
        }
    }

    @Nested
    inner class CreateEmptyMacroCellTests {

        @Test
        fun `create empty macro cell at negative level throws`() {
            assertFailsWith<IllegalArgumentException> {
                createEmptyMacroCell(-1)
            }
        }

        @Test
        fun `create empty macro cell at level 0 is correct`() {
            assertEquals(
                MacroCell.Cell.DeadCell,
                createEmptyMacroCell(0)
            )
        }

        @Test
        fun `create empty macro cell at level 1 is correct`() {
            assertEquals(
                MacroCell.CellNode(
                    MacroCell.Cell.DeadCell,
                    MacroCell.Cell.DeadCell,
                    MacroCell.Cell.DeadCell,
                    MacroCell.Cell.DeadCell
                ),
                createEmptyMacroCell(1)
            )
        }

        @Test
        fun `create empty macro cell at level 2 is correct`() {
            assertEquals(
                MacroCell.CellNode(
                    MacroCell.CellNode(
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell
                    ),
                    MacroCell.CellNode(
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell
                    ),
                    MacroCell.CellNode(
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell
                    ),
                    MacroCell.CellNode(
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell,
                        MacroCell.Cell.DeadCell
                    ),
                ),
                createEmptyMacroCell(2)
            )
        }

        @Test
        fun `create empty macro cell at level 3 is correct`() {
            assertEquals(
                MacroCell.CellNode(
                    MacroCell.CellNode(
                        MacroCell.CellNode(
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell
                        ),
                        MacroCell.CellNode(
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell
                        ),
                        MacroCell.CellNode(
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell
                        ),
                        MacroCell.CellNode(
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell
                        ),
                    ),
                    MacroCell.CellNode(
                        MacroCell.CellNode(
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell
                        ),
                        MacroCell.CellNode(
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell
                        ),
                        MacroCell.CellNode(
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell
                        ),
                        MacroCell.CellNode(
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell
                        ),
                    ),
                    MacroCell.CellNode(
                        MacroCell.CellNode(
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell
                        ),
                        MacroCell.CellNode(
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell
                        ),
                        MacroCell.CellNode(
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell
                        ),
                        MacroCell.CellNode(
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell
                        ),
                    ),
                    MacroCell.CellNode(
                        MacroCell.CellNode(
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell
                        ),
                        MacroCell.CellNode(
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell
                        ),
                        MacroCell.CellNode(
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell
                        ),
                        MacroCell.CellNode(
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell,
                            MacroCell.Cell.DeadCell
                        ),
                    ),
                ),
                createEmptyMacroCell(3)
            )
        }
    }

    @Nested
    inner class ContainsTests {
        @Test
        fun `checking contains specific cell is correct`() {
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
                                MacroCell.Cell.AliveCell
                            ),
                            createEmptyMacroCell(1),
                            createEmptyMacroCell(1),
                            createEmptyMacroCell(1),
                        ),
                        createEmptyMacroCell(2),
                    ),
                    createEmptyMacroCell(3),
                    createEmptyMacroCell(3),
                ).contains(IntOffset(9, 5))
            )
        }

        @Test
        fun `checking does not contain specific cell is correct`() {
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
                                MacroCell.Cell.AliveCell
                            ),
                            createEmptyMacroCell(1),
                            createEmptyMacroCell(1),
                            createEmptyMacroCell(1),
                        ),
                        createEmptyMacroCell(2),
                    ),
                    createEmptyMacroCell(3),
                    createEmptyMacroCell(3),
                ).contains(IntOffset(9, 6))
            )
        }

        @Test
        fun `checking does not contain outside range cell is correct`() {
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
                                MacroCell.Cell.AliveCell
                            ),
                            createEmptyMacroCell(1),
                            createEmptyMacroCell(1),
                            createEmptyMacroCell(1),
                        ),
                        createEmptyMacroCell(2),
                    ),
                    createEmptyMacroCell(3),
                    createEmptyMacroCell(3),
                ).contains(IntOffset(-2, -2))
            )
        }
    }
}
