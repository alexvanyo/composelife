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

class Life106CellStateSerializerTests {

    private val serializer = Life106CellStateSerializer

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
                format = CellStateFormat.FixedFormat.Life106,
            ),
            serializer.deserializeToCellState(
                """
                |#Life 1.06
                |0 0
                |2 0
                |4 0
                |0 2
                |2 2
                |4 2
                |0 4
                |2 4
                |4 4
                """.trimMargin().lineSequence(),
            ),
        )
    }

    @Test
    fun basic_serialization_is_correct() {
        assertEquals(
            """
            |#Life 1.06
            |0 0
            |2 0
            |4 0
            |0 2
            |2 2
            |4 2
            |0 4
            |2 4
            |4 4
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
