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

import com.alexvanyo.composelife.model.CellStateSerializer.DeserializationResult
import com.alexvanyo.composelife.patterns.GameOfLifeTestPattern
import com.alexvanyo.composelife.patterns.GameOfLifeTestPatternEnum
import com.alexvanyo.composelife.patterns.sealedObject
import com.google.testing.junit.testparameterinjector.junit5.TestParameter
import com.google.testing.junit.testparameterinjector.junit5.TestParameterInjectorTest
import kotlin.test.assertEquals
import kotlin.test.assertIs
import kotlin.test.assertTrue

class SerializerTests {

    class CellStateSerializerFactory(
        private val name: String,
        val trueEquals: Boolean,
        val factory: () -> CellStateSerializer,
    ) {
        override fun toString(): String = name

        class Provider : TestParameter.TestParameterValuesProvider {
            override fun provideValues() =
                listOf(
                    CellStateSerializerFactory(
                        name = "Plaintext",
                        trueEquals = false,
                    ) {
                        PlaintextCellStateSerializer()
                    },
                    CellStateSerializerFactory(
                        name = "Life 1.05",
                        trueEquals = true,
                    ) {
                        Life105CellStateSerializer()
                    },
                )
        }
    }

    @TestParameter(valuesProvider = CellStateSerializerFactory.Provider::class)
    lateinit var serializerFactory: CellStateSerializerFactory

    @TestParameter
    lateinit var testPatternEnum: GameOfLifeTestPatternEnum

    private val testPattern: GameOfLifeTestPattern get() = testPatternEnum.sealedObject

    /**
     * Checks the serialization invariant for all test patterns: serializing the pattern and then deserializing it
     * results in the original pattern, with no warnings.
     *
     * Some serializers won't be able to preserve the original offset: For those serializers,
     * `CellStateSerializerFactory.trueEquals` is false, and equality is checked modulo the offset.
     */
    @TestParameterInjectorTest
    fun `serializing and deserializing is successful`() {
        val serializer = serializerFactory.factory()

        val serialized = serializer.serializeToString(testPattern.seedCellState)
        val deserializationResult = serializer.deserializeToCellState(serialized)

        assertIs<DeserializationResult.Successful>(deserializationResult)

        assertEquals(emptyList(), deserializationResult.warnings)
        if (serializerFactory.trueEquals) {
            assertEquals(testPattern.seedCellState, deserializationResult.cellState)
        } else {
            assertTrue(testPattern.seedCellState.equalsModuloOffset(deserializationResult.cellState))
        }
    }
}
