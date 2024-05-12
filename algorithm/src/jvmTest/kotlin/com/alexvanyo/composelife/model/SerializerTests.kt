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

import com.alexvanyo.composelife.patterns.GameOfLifeTestPattern
import com.alexvanyo.composelife.patterns.GameOfLifeTestPatternEnum
import com.alexvanyo.composelife.patterns.values
import de.infix.testBalloon.framework.core.testSuite
import kotlin.test.assertEquals
import kotlin.test.assertIs
import kotlin.test.assertTrue

private class CellStateSerializerFactory(
    private val name: String,
    val trueEquals: Boolean,
    val format: CellStateFormat.FixedFormat,
    val factory: () -> FixedFormatCellStateSerializer,
) {
    override fun toString(): String = name
}

val SerializerTests by testSuite {
    val cellStateSerializerFactories = listOf(
        CellStateSerializerFactory(
            name = "Plaintext",
            trueEquals = false,
            format = CellStateFormat.FixedFormat.Plaintext,
        ) {
            PlaintextCellStateSerializer
        },
        CellStateSerializerFactory(
            name = "Life 1.05",
            trueEquals = true,
            format = CellStateFormat.FixedFormat.Life105,
        ) {
            Life105CellStateSerializer
        },
        CellStateSerializerFactory(
            name = "Life 1.06",
            trueEquals = true,
            format = CellStateFormat.FixedFormat.Life106,
        ) {
            Life106CellStateSerializer
        },
        CellStateSerializerFactory(
            name = "Run length encoding",
            trueEquals = true,
            format = CellStateFormat.FixedFormat.RunLengthEncoding,
        ) {
            RunLengthEncodedCellStateSerializer
        },
        CellStateSerializerFactory(
            name = "Macrocell",
            trueEquals = false,
            format = CellStateFormat.FixedFormat.Macrocell,
        ) {
            MacrocellCellStateSerializer
        },
    )

    val testPatterns = GameOfLifeTestPattern.values

    cellStateSerializerFactories.forEach { cellStateSerializerFactory ->
        testSuite(cellStateSerializerFactory.toString()) {
            testPatterns.forEach { testPattern ->
                testSuite(testPattern.toString()) {
                    /**
                     * Checks the serialization invariant for all test patterns: serializing the pattern and then
                     * deserializing it results in the original pattern, with no warnings.
                     *
                     * Some serializers won't be able to preserve the original offset: For those serializers,
                     * CellStateSerializerFactory.trueEquals is false, and equality is checked modulo the offset.
                     */
                    test("serializing_and_deserializing_is_successful") {
                        val serializer = cellStateSerializerFactory.factory()

                        val serialized = serializer.serializeToString(testPattern.seedCellState)
                        val deserializationResult = serializer.deserializeToCellState(serialized)

                        val _ = assertIs<DeserializationResult.Successful>(deserializationResult)

                        assertEquals(emptyList(), deserializationResult.warnings)
                        if (cellStateSerializerFactory.trueEquals) {
                            assertEquals(testPattern.seedCellState, deserializationResult.cellState)
                        } else {
                            assertTrue(testPattern.seedCellState.equalsModuloOffset(deserializationResult.cellState))
                        }
                        assertEquals(cellStateSerializerFactory.format, deserializationResult.format)
                    }
                }
            }
        }
    }
}
