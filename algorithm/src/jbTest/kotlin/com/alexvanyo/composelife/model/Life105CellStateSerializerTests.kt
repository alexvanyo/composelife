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

import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertIs

@Suppress("TooManyFunctions")
class Life105CellStateSerializerTests {
    private val serializer = Life105CellStateSerializer

    @Test
    fun basic_deserialization_is_correct() {
        assertEquals(
            DeserializationResult.Successful(
                warnings = emptyList(),
                cellState = setOf(
                    0 to 0,
                    2 to 0,
                    4 to 0,
                    0 to 2,
                    2 to 2,
                    4 to 2,
                    0 to 4,
                    2 to 4,
                    4 to 4,
                ).toCellState(),
                format = CellStateFormat.FixedFormat.Life105,
            ),
            serializer.deserializeToCellState(
                """
                |#Life 1.05
                |#N
                |#P 0 0
                |*.*.*
                |.....
                |*.*.*
                |.....
                |*.*.*
                """.trimMargin().lineSequence(),
            ),
        )
    }

    @Test
    fun deserialization_empty_file_returns_successful_with_warning() {
        val result = serializer.deserializeToCellState(emptySequence())
        val successfulResult = assertIs<DeserializationResult.Successful>(result)
        assertEquals(listOf(UnexpectedEmptyFileMessage), successfulResult.warnings)
        assertEquals(emptyCellState(), successfulResult.cellState)
        assertEquals(CellStateFormat.FixedFormat.Life105, successfulResult.format)
    }

    @Test
    fun deserialization_invalid_header_returns_unsuccessful() {
        val result = serializer.deserializeToCellState(sequenceOf("#Life 1.06"))
        val unsuccessfulResult = assertIs<DeserializationResult.Unsuccessful>(result)
        assertEquals(listOf(UnexpectedHeaderMessage("#Life 1.06")), unsuccessfulResult.errors)
    }

    @Test
    fun deserialization_description_lines_are_ignored() {
        assertEquals(
            DeserializationResult.Successful(
                warnings = emptyList(),
                cellState = setOf(
                    0 to 0,
                ).toCellState(),
                format = CellStateFormat.FixedFormat.Life105,
            ),
            serializer.deserializeToCellState(
                """
                |#Life 1.05
                |#D First description
                |#D Second description
                |#N
                |#P 0 0
                |*
                """.trimMargin().lineSequence(),
            ),
        )
    }

    @Test
    fun deserialization_unexpected_ruleset_normal_warning() {
        val result = serializer.deserializeToCellState(
            """
            |#Life 1.05
            |#N extra
            |#P 0 0
            |*
            """.trimMargin().lineSequence(),
        )
        val successfulResult = assertIs<DeserializationResult.Successful>(result)
        assertEquals(
            listOf(UnexpectedInputMessage("#N extra", 2, 3)),
            successfulResult.warnings,
        )
        assertEquals(setOf(0 to 0).toCellState(), successfulResult.cellState)
    }

    @Test
    fun deserialization_ruleset_rule_23_3_is_supported() {
        assertEquals(
            DeserializationResult.Successful(
                warnings = emptyList(),
                cellState = setOf(
                    0 to 0,
                ).toCellState(),
                format = CellStateFormat.FixedFormat.Life105,
            ),
            serializer.deserializeToCellState(
                """
                |#Life 1.05
                |#R 23/3
                |#P 0 0
                |*
                """.trimMargin().lineSequence(),
            ),
        )
    }

    @Test
    fun deserialization_ruleset_rule_malformed_returns_unsuccessful() {
        val result = serializer.deserializeToCellState(
            """
            |#Life 1.05
            |#R invalid
            |#P 0 0
            |*
            """.trimMargin().lineSequence(),
        )
        val unsuccessfulResult = assertIs<DeserializationResult.Unsuccessful>(result)
        assertEquals(
            listOf(UnexpectedInputMessage("#R invalid", 2, 3)),
            unsuccessfulResult.errors,
        )
    }

    @Test
    fun deserialization_ruleset_unsupported_rule_returns_unsuccessful() {
        val result = serializer.deserializeToCellState(
            """
            |#Life 1.05
            |#R 23/4
            |#P 0 0
            |*
            """.trimMargin().lineSequence(),
        )
        val unsuccessfulResult = assertIs<DeserializationResult.Unsuccessful>(result)
        assertEquals(
            listOf(RuleNotSupportedMessage),
            unsuccessfulResult.errors,
        )
    }

    @Test
    fun deserialization_no_rule_line_is_correct() {
        assertEquals(
            DeserializationResult.Successful(
                warnings = emptyList(),
                cellState = setOf(
                    0 to 0,
                ).toCellState(),
                format = CellStateFormat.FixedFormat.Life105,
            ),
            serializer.deserializeToCellState(
                """
                |#Life 1.05
                |#P 0 0
                |*
                """.trimMargin().lineSequence(),
            ),
        )
    }

    @Test
    fun deserialization_row_before_block_returns_unsuccessful() {
        val result = serializer.deserializeToCellState(
            """
            |#Life 1.05
            |#N
            |*
            """.trimMargin().lineSequence(),
        )
        val unsuccessfulResult = assertIs<DeserializationResult.Unsuccessful>(result)
        assertEquals(
            listOf(UnexpectedInputMessage("*", 3, 1)),
            unsuccessfulResult.errors,
        )
    }

    @Test
    fun deserialization_malformed_block_header_returns_unsuccessful() {
        val result = serializer.deserializeToCellState(
            """
            |#Life 1.05
            |#N
            |#P 0
            """.trimMargin().lineSequence(),
        )
        val unsuccessfulResult = assertIs<DeserializationResult.Unsuccessful>(result)
        assertEquals(
            listOf(UnexpectedInputMessage("#P 0", 3, 3)),
            unsuccessfulResult.errors,
        )
    }

    @Test
    fun deserialization_malformed_line_returns_unsuccessful() {
        val result = serializer.deserializeToCellState(
            """
            |#Life 1.05
            |#N
            |#P 0 0
            |invalid
            """.trimMargin().lineSequence(),
        )
        val unsuccessfulResult = assertIs<DeserializationResult.Unsuccessful>(result)
        assertEquals(
            listOf(UnexpectedInputMessage("invalid", 4, 1)),
            unsuccessfulResult.errors,
        )
    }

    @Test
    fun basic_serialization_is_correct() {
        assertEquals(
            """
            |#Life 1.05
            |#N
            |#P 0 0
            |*.*.*...........................................................................
            |................................................................................
            |*.*.*...........................................................................
            |................................................................................
            |*.*.*...........................................................................
            """.trimMargin(),
            serializer.serializeToString(
                setOf(
                    0 to 0,
                    2 to 0,
                    4 to 0,
                    0 to 2,
                    2 to 2,
                    4 to 2,
                    0 to 4,
                    2 to 4,
                    4 to 4,
                ).toCellState(),
            ).joinToString("\n"),
        )
    }
}
