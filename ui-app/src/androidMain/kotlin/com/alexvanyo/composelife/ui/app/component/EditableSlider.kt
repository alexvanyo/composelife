/*
 * Copyright 2023 The Android Open Source Project
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

package com.alexvanyo.composelife.ui.app.component

import androidx.compose.foundation.focusable
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.text.KeyboardActions
import androidx.compose.foundation.text.KeyboardOptions
import androidx.compose.material3.ExperimentalMaterial3Api
import androidx.compose.material3.SliderColors
import androidx.compose.material3.SliderDefaults
import androidx.compose.material3.Text
import androidx.compose.material3.TextField
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import androidx.compose.ui.Modifier
import androidx.compose.ui.focus.FocusRequester
import androidx.compose.ui.focus.focusRequester
import androidx.compose.ui.focus.onFocusChanged
import androidx.compose.ui.text.input.ImeAction
import androidx.compose.ui.text.input.KeyboardType
import java.util.UUID

@OptIn(ExperimentalMaterial3Api::class)
@Suppress("LongParameterList", "LongMethod")
@Composable
fun <T : Comparable<T>> EditableSlider(
    labelAndValueText: @Composable (T) -> String,
    valueText: @Composable (T) -> String,
    labelText: String,
    textToValue: (String) -> T?,
    value: T,
    onValueChange: (T) -> Unit,
    valueRange: ClosedRange<T>,
    sliderBijection: SliderBijection<T>,
    modifier: Modifier = Modifier,
    enabled: Boolean = true,
    steps: Int = 0,
    onValueChangeFinished: (() -> Unit)? = null,
    colors: SliderColors = SliderDefaults.colors(),
    sliderOverlay: @Composable () -> Unit = {},
    keyboardType: KeyboardType = KeyboardType.Decimal,
) {
    var isTextEditing by rememberSaveable { mutableStateOf(false) }
    val nonTransientValueText = valueText(value)
    var knownTransientValue by remember { mutableStateOf(value) }
    var editingSessionKey by remember {
        mutableStateOf(UUID.randomUUID())
    }
    val didValueUpdateOutOfBand = knownTransientValue != value
    key(didValueUpdateOutOfBand) {
        if (didValueUpdateOutOfBand) {
            editingSessionKey = UUID.randomUUID()
            knownTransientValue = value
        }
    }
    var transientTextFieldValue by rememberSaveable(
        isTextEditing,
        editingSessionKey,
    ) {
        mutableStateOf(nonTransientValueText)
    }

    fun getTransientValue(): T? = textToValue(transientTextFieldValue)?.coerceIn(valueRange)

    val currentValue = getTransientValue() ?: value
    val sliderFocusRequester = remember { FocusRequester() }
    val textFieldFocusRequester = remember { FocusRequester() }

    LabeledSlider(
        label = labelAndValueText(currentValue),
        value = currentValue,
        onValueChange = onValueChange,
        valueRange = valueRange,
        sliderBijection = sliderBijection,
        modifier = modifier
            .focusRequester(sliderFocusRequester)
            .focusable(),
        enabled = enabled,
        steps = steps,
        onValueChangeFinished = onValueChangeFinished,
        colors = colors,
        labelSlot = {
            TextField(
                value = transientTextFieldValue,
                onValueChange = { value ->
                    transientTextFieldValue = value
                    getTransientValue()?.let { transientValue ->
                        onValueChange(transientValue)
                        knownTransientValue = transientValue
                    }
                },
                modifier = Modifier
                    .fillMaxWidth()
                    .focusRequester(textFieldFocusRequester)
                    .onFocusChanged {
                        isTextEditing = !it.isFocused
                        val transientValue = getTransientValue()
                        if (!it.isFocused && transientValue != null) {
                            onValueChange(transientValue)
                            onValueChangeFinished?.invoke()
                        }
                    },
                label = {
                    Text(labelText)
                },
                placeholder = {
                    Text(nonTransientValueText)
                },
                isError = getTransientValue() == null,
                keyboardOptions = KeyboardOptions(
                    keyboardType = keyboardType,
                    imeAction = ImeAction.Done,
                ),
                keyboardActions = KeyboardActions(
                    onDone = {
                        sliderFocusRequester.requestFocus()
                    }
                ),
                singleLine = true,
            )
        },
        sliderOverlay = sliderOverlay,
    )
}
