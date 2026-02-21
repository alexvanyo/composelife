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
            ).contains(IntOffset(19, 15)),
        )
    }

    @Test
    fun checking_does_not_contain_specific_cell_is_correct() {
        assertFalse(
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
            ).contains(IntOffset(19, 16)),
        )
    }

    @Test
    fun checking_does_not_contain_outside_range_cell_is_correct() {
        assertFalse(
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
            ).contains(IntOffset(-2, -2)),
        )
    }
}
