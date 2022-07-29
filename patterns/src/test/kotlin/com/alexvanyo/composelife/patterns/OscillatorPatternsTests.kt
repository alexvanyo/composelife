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

package com.alexvanyo.composelife.patterns

import androidx.compose.ui.unit.IntRect
import com.google.testing.junit.testparameterinjector.junit5.TestParameter
import com.google.testing.junit.testparameterinjector.junit5.TestParameterInjectorTest
import kotlin.test.assertEquals

class OscillatorPatternsTests {

    @TestParameter
    lateinit var oscillatorPatternEnum: OscillatorPatternEnum

    private val oscillatorPattern get() = oscillatorPatternEnum.sealedObject

    /**
     * Check that the list of repeating states are distinct.
     *
     * This ensures that the period is minimal.
     *
     * The oscillator patterns are used to verify the algorithm, so those checks will actually
     * ensure the pattern does oscillate.
     */
    @TestParameterInjectorTest
    fun `list of states are distinct`() {
        val repeatingCellStates =
            listOf(oscillatorPattern.seedCellState) + oscillatorPattern.otherCellStates

        assertEquals(
            oscillatorPattern.period,
            repeatingCellStates.distinct().size,
        )
    }

    @TestParameterInjectorTest
    fun `bounding box is minimal and correct`() {
        val repeatingCellStates =
            listOf(oscillatorPattern.seedCellState) + oscillatorPattern.otherCellStates

        assertEquals(
            oscillatorPattern.boundingBox,
            repeatingCellStates.fold(null) { acc: IntRect?, cellState ->
                val boundingBox = cellState.boundingBox
                if (acc == null) {
                    boundingBox
                } else {
                    IntRect(
                        left = minOf(boundingBox.left, acc.left),
                        top = minOf(boundingBox.top, acc.top),
                        right = maxOf(boundingBox.right, acc.right),
                        bottom = maxOf(boundingBox.bottom, acc.bottom),
                    )
                }
            },
        )
    }
}
