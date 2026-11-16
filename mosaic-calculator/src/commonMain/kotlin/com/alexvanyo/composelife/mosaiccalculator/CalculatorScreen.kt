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

import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.setValue
import com.jakewharton.mosaic.layout.onKeyEvent
import com.jakewharton.mosaic.modifier.Modifier
import com.jakewharton.mosaic.ui.Column
import com.jakewharton.mosaic.ui.Row
import com.jakewharton.mosaic.ui.Text

/**
 * Stateful Compose root wrapping [CalculatorScreen] with remembered snapshot state.
 */
@Composable
fun CalculatorApp(initialState: CalculatorState = CalculatorState.Initial, modifier: Modifier = Modifier) {
    var state by remember { mutableStateOf(initialState) }
    CalculatorScreen(
        state = state,
        onKey = { key ->
            state = reduceCalculatorState(state, key)
        },
        modifier = modifier,
    )
}

/**
 * Stateless terminal calculator UI built from Mosaic primitives (`Column`, `Row`, `Text`, `onKeyEvent`).
 */
@Composable
fun CalculatorScreen(state: CalculatorState, onKey: (CalculatorKey) -> Unit, modifier: Modifier = Modifier) {
    Column(
        modifier = modifier.onKeyEvent { event ->
            val mapped = mapTerminalKey(event.key)
            if (mapped != null) {
                onKey(mapped)
                true
            } else {
                false
            }
        },
    ) {
        Text("=== Calculator ===")
        Text("> ${formatDisplayLine(state)}")
        Row {
            Text("[7] [8] [9] [/]")
        }
        Row {
            Text("[4] [5] [6] [*]")
        }
        Row {
            Text("[1] [2] [3] [-]")
        }
        Row {
            Text("[0] [C] [=] [+]")
        }
    }
}
