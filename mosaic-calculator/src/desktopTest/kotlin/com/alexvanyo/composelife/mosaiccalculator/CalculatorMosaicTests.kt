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

package com.alexvanyo.composelife.mosaiccalculator

import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import com.jakewharton.mosaic.terminal.KeyboardEvent
import com.jakewharton.mosaic.testing.runMosaicTest
import kotlinx.coroutines.test.runTest
import kotlin.test.Test
import kotlin.test.assertEquals

class CalculatorMosaicTests {
    @Test
    fun calculator_screen_renders_initial_and_updated_state() = runTest {
        runMosaicTest {
            var state by mutableStateOf(CalculatorState.Initial)
            setContent {
                CalculatorScreen(
                    state = state,
                    onKey = { key ->
                        state = reduceCalculatorState(state, key)
                    },
                )
            }
            assertEquals(
                """
                |=== Calculator ===
                |> 0
                |[7] [8] [9] [/]
                |[4] [5] [6] [*]
                |[1] [2] [3] [-]
                |[0] [C] [=] [+]
                """.trimMargin(),
                awaitSnapshot(),
            )

            state = reduceCalculatorState(state, CalculatorKey.Digit(1))
            state = reduceCalculatorState(state, CalculatorKey.Digit(2))
            state = reduceCalculatorState(state, CalculatorKey.Op(CalculatorOp.Add))
            assertEquals(
                """
                |=== Calculator ===
                |> 12 +
                |[7] [8] [9] [/]
                |[4] [5] [6] [*]
                |[1] [2] [3] [-]
                |[0] [C] [=] [+]
                """.trimMargin(),
                awaitSnapshot(),
            )

            state = reduceCalculatorState(state, CalculatorKey.Digit(3))
            assertEquals(
                """
                |=== Calculator ===
                |> 12 + 3
                |[7] [8] [9] [/]
                |[4] [5] [6] [*]
                |[1] [2] [3] [-]
                |[0] [C] [=] [+]
                """.trimMargin(),
                awaitSnapshot(),
            )

            state = reduceCalculatorState(state, CalculatorKey.Equals)
            assertEquals(
                """
                |=== Calculator ===
                |> 15
                |[7] [8] [9] [/]
                |[4] [5] [6] [*]
                |[1] [2] [3] [-]
                |[0] [C] [=] [+]
                """.trimMargin(),
                awaitSnapshot(),
            )
        }
    }

    @Test
    fun calculator_app_processes_terminal_key_events_and_recomposes() = runTest {
        runMosaicTest {
            setContent {
                CalculatorApp()
            }
            assertEquals(
                """
                |=== Calculator ===
                |> 0
                |[7] [8] [9] [/]
                |[4] [5] [6] [*]
                |[1] [2] [3] [-]
                |[0] [C] [=] [+]
                """.trimMargin(),
                awaitSnapshot(),
            )

            sendKeyEvent(KeyboardEvent(codepoint = '4'.code))
            sendKeyEvent(KeyboardEvent(codepoint = '2'.code))
            sendKeyEvent(KeyboardEvent(codepoint = '-'.code))
            sendKeyEvent(KeyboardEvent(codepoint = '7'.code))
            sendKeyEvent(KeyboardEvent(codepoint = '='.code))
            assertEquals(
                """
                |=== Calculator ===
                |> 35
                |[7] [8] [9] [/]
                |[4] [5] [6] [*]
                |[1] [2] [3] [-]
                |[0] [C] [=] [+]
                """.trimMargin(),
                awaitSnapshot(),
            )
        }
    }
}
