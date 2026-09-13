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

package com.alexvanyo.composelife.model

import androidx.compose.ui.unit.IntOffset
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFailsWith
import kotlin.test.assertNotNull
import kotlin.test.assertTrue

class CellStateSerializationTests {

    @Test
    fun to_cell_state_default_parameters_successful() {
        val cellState = """
            |..O
            |O.O
            |.OO
        """.toCellState()

        assertEquals(
            setOf(
                IntOffset(2, 0),
                IntOffset(0, 1),
                IntOffset(2, 1),
                IntOffset(1, 2),
                IntOffset(2, 2),
            ),
            cellState.aliveCells,
        )
    }

    @Test
    fun to_cell_state_with_top_left_offset() {
        val cellState = """
            |O
        """.toCellState(
            topLeftOffset = IntOffset(5, 10),
        )

        assertEquals(
            setOf(
                IntOffset(5, 10),
            ),
            cellState.aliveCells,
        )
    }

    @Test
    fun to_cell_state_with_warnings_throw_on_warnings_true_throws() {
        val exception = assertFailsWith<IllegalStateException> {
            """
                |?
            """.toCellState(
                throwOnWarnings = true,
            )
        }

        val message = exception.message
        assertNotNull(message)
        assertTrue(message.startsWith("Warnings when parsing cell state!"))
    }

    @Test
    fun to_cell_state_with_warnings_throw_on_warnings_false_succeeds() {
        val cellState = """
            |?
        """.toCellState(
            throwOnWarnings = false,
        )

        assertEquals(
            setOf(
                IntOffset(0, 0),
            ),
            cellState.aliveCells,
        )
    }

    @Test
    fun to_cell_state_unsuccessful_throws() {
        val exception = assertFailsWith<IllegalStateException> {
            """
                |bad header
                |1 2
            """.toCellState(
                fixedFormatCellStateSerializer = Life106CellStateSerializer,
            )
        }

        val message = exception.message
        assertNotNull(message)
        assertTrue(message.startsWith("Could not parse cell state!"))
    }
}
