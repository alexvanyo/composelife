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

package com.alexvanyo.composelife.patterns

import kotlin.test.Test
import kotlin.test.assertEquals

class PatternSealedEnumTests {

    @Test
    fun game_of_life_test_pattern_enum_values_and_value_of_are_correct() {
        val expectedValues = GameOfLifeTestPattern.sealedEnum.values.map { pattern ->
            GameOfLifeTestPatternEnum.entries.first { it.sealedObject == pattern }
        }
        assertEquals(expectedValues, GameOfLifeTestPatternEnum.entries)
        assertEquals(expectedValues, GameOfLifeTestPatternEnum.values().toList())
        expectedValues.forEach { enumValue ->
            assertEquals(enumValue, GameOfLifeTestPatternEnum.valueOf(enumValue.name))
        }
    }

    @Test
    fun methuselah_pattern_enum_values_and_value_of_are_correct() {
        val expectedValues = MethuselahPattern.sealedEnum.values.map { pattern ->
            MethuselahPatternEnum.entries.first { it.sealedObject == pattern }
        }
        assertEquals(expectedValues, MethuselahPatternEnum.entries)
        assertEquals(expectedValues, MethuselahPatternEnum.values().toList())
        expectedValues.forEach { enumValue ->
            assertEquals(enumValue, MethuselahPatternEnum.valueOf(enumValue.name))
        }
    }
}
