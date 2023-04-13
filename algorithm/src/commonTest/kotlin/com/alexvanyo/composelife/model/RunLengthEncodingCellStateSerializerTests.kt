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

class RunLengthEncodingCellStateSerializerTests {

    private val serializer = RunLengthEncodedCellStateSerializer

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
                format = CellStateFormat.FixedFormat.RunLengthEncoding,
            ),
            serializer.deserializeToCellState(
                """
                |x = 5, y = 5, rule = B3/S23
                |obobo${'$'}${'$'}obobo${'$'}${'$'}obobo!
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
                format = CellStateFormat.FixedFormat.RunLengthEncoding,
            ),
            serializer.deserializeToCellState(
                """
                |#C This is a comment
                |x = 5, y = 5, rule = B3/S23
                |obobo${'$'}${'$'}obobo${'$'}${'$'}obobo!
                """.trimMargin().lineSequence(),
            ),
        )
    }

    @Test
    fun deserialization_with_top_left_offset_with_R_is_correct() {
        assertEquals(
            DeserializationResult.Successful(
                warnings = emptyList(),
                cellState = setOf(
                    -3 to 7,
                    -1 to 7,
                    1 to 7,
                    -3 to 9,
                    -1 to 9,
                    1 to 9,
                    -3 to 11,
                    -1 to 11,
                    1 to 11,
                ).toCellState(),
                format = CellStateFormat.FixedFormat.RunLengthEncoding,
            ),
            serializer.deserializeToCellState(
                """
                |#R -3 7
                |x = 5, y = 5, rule = B3/S23
                |obobo${'$'}${'$'}obobo${'$'}${'$'}obobo!
                """.trimMargin().lineSequence(),
            ),
        )
    }

    @Test
    fun deserialization_with_top_left_offset_with_P_is_correct() {
        assertEquals(
            DeserializationResult.Successful(
                warnings = emptyList(),
                cellState = setOf(
                    -3 to 7,
                    -1 to 7,
                    1 to 7,
                    -3 to 9,
                    -1 to 9,
                    1 to 9,
                    -3 to 11,
                    -1 to 11,
                    1 to 11,
                ).toCellState(),
                format = CellStateFormat.FixedFormat.RunLengthEncoding,
            ),
            serializer.deserializeToCellState(
                """
                |#P -3 7
                |x = 5, y = 5, rule = B3/S23
                |obobo${'$'}${'$'}obobo${'$'}${'$'}obobo!
                """.trimMargin().lineSequence(),
            ),
        )
    }

    @Test
    fun basic_serialization_is_correct() {
        assertEquals(
            """
            |#R 0 0
            |x = 5, y = 5, rule = B3/S23
            |obobo${'$'}${'$'}obobo${'$'}${'$'}obobo!
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

    @Test
    fun gosper_glider_gun_serialization_is_correct() {
        assertEquals(
            """
            |#R 0 0
            |x = 36, y = 9, rule = B3/S23
            |24bo${'$'}22bobo${'$'}12b2o6b2o12b2o${'$'}11bo3bo4b2o12b2o${'$'}2o8bo5bo3b2o${'$'}2o8bo3bob2o4b
            |obo${'$'}10bo5bo7bo${'$'}11bo3bo${'$'}12b2o!
            """.trimMargin(),
            serializer.serializeToString(
                """
                |........................O...........
                |......................O.O...........
                |............OO......OO............OO
                |...........O...O....OO............OO
                |OO........O.....O...OO..............
                |OO........O...O.OO....O.O...........
                |..........O.....O.......O...........
                |...........O...O....................
                |............OO......................
                """.toCellState(),
            ).joinToString("\n"),
        )
    }
}
