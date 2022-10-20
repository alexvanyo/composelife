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

import kotlin.test.Test
import kotlin.test.assertEquals

class PlaintextCellStateSerializerTests {

    private val serializer = PlaintextCellStateSerializer

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
            ),
            serializer.deserializeToCellState(
                """
                |O.O.O.
                |......
                |O.O.O.
                |......
                |O.O.O.
                |......
                |
                """.trimMargin().lineSequence(),
            ),
        )
    }

    @Test
    fun deserialization_with_comments_is_correct() {
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
            ),
            serializer.deserializeToCellState(
                """
                |! comment 1
                |! comment 2
                |O.O.O.
                |......
                |! comment 3
                |O.O.O.
                |......
                |O.O.O.
                |......
                |! comment 4
                |
                """.trimMargin().lineSequence(),
            ),
        )
    }

    @Test
    fun deserialization_with_comments_and_warnings_is_correct() {
        assertEquals(
            DeserializationResult.Successful(
                warnings = listOf(
                    UnexpectedBlankLineMessage(3),
                    UnexpectedCharacterMessage('0', 4, 1),
                    UnexpectedCharacterMessage('0', 4, 3),
                    UnexpectedCharacterMessage('0', 4, 5),
                    UnexpectedShortLineMessage(4),
                    UnexpectedCharacterMessage('0', 7, 1),
                    UnexpectedCharacterMessage('0', 7, 3),
                    UnexpectedCharacterMessage('0', 7, 5),
                    UnexpectedShortLineMessage(9),
                    UnexpectedCharacterMessage('0', 9, 1),
                    UnexpectedCharacterMessage(' ', 9, 2),
                    UnexpectedCharacterMessage('0', 9, 3),
                    UnexpectedCharacterMessage(' ', 9, 4),
                    UnexpectedCharacterMessage('0', 9, 5),
                ),
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
            ),
            serializer.deserializeToCellState(
                """
                |! comment 1
                |! comment 2
                |
                |0.0.0
                |......
                |! comment 3
                |0.0.0.
                |......
                |0 0 0
                |......
                |! comment 4
                |
                """.trimMargin().lineSequence(),
            ),
        )
    }

    @Test
    fun basic_serialization_is_correct() {
        assertEquals(
            """
            |O.O.O
            |.....
            |O.O.O
            |.....
            |O.O.O
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
