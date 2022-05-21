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
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.EnumSource
import kotlin.test.assertEquals

class OscillatorPatternsTests {

    /**
     * Check that the list of repeating states are distinct.
     *
     * This ensures that the period is minimal.
     *
     * The oscillator patterns are used to verify the algorithm, so those checks will actually
     * ensure the pattern does oscillate.
     */
    @ParameterizedTest
    @EnumSource(OscillatorPatternEnum::class)
    fun `list of states are distinct`(oscillatorPatternEnum: OscillatorPatternEnum) {
        val oscillatorPattern = oscillatorPatternEnum.sealedObject
        val repeatingCellStates =
            listOf(oscillatorPattern.seedCellState) + oscillatorPattern.otherCellStates

        assertEquals(
            oscillatorPattern.period,
            repeatingCellStates.distinct().size,
        )
    }

    @ParameterizedTest
    @EnumSource(OscillatorPatternEnum::class)
    fun `bounding box is minimal and correct`(oscillatorPatternEnum: OscillatorPatternEnum) {
        val oscillatorPattern = oscillatorPatternEnum.sealedObject
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
