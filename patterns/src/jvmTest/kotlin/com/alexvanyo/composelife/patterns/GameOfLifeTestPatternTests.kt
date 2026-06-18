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

import com.google.testing.junit.testparameterinjector.TestParameter
import com.google.testing.junit.testparameterinjector.TestParameterInjector
import org.junit.runner.RunWith
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

@RunWith(TestParameterInjector::class)
class GameOfLifeTestPatternTests {

    @TestParameter
    lateinit var patternEnum: GameOfLifeTestPatternEnum

    private val pattern get() = patternEnum.sealedObject

    @Test
    fun pattern_name_is_non_empty() {
        assertFalse(pattern.patternName.isEmpty())
    }

    @Test
    fun max_generation_cell_state_is_correct() {
        assertEquals(
            pattern.cellStates.keys.maxOrNull() ?: 0,
            pattern.maxGenerationCellState,
        )
    }

    @Test
    fun to_string_is_non_blank() {
        assertTrue(pattern.toString().isNotBlank())
    }
}
