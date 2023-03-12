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

package com.alexvanyo.composelife.ui.app.action

import androidx.compose.foundation.Canvas
import androidx.compose.foundation.ScrollState
import androidx.compose.foundation.focusable
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.layout.padding
import androidx.compose.foundation.rememberScrollState
import androidx.compose.foundation.text.KeyboardActions
import androidx.compose.foundation.text.KeyboardOptions
import androidx.compose.foundation.verticalScroll
import androidx.compose.material3.ExperimentalMaterial3Api
import androidx.compose.material3.MaterialTheme
import androidx.compose.material3.Surface
import androidx.compose.material3.Text
import androidx.compose.material3.TextField
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import androidx.compose.ui.Modifier
import androidx.compose.ui.focus.FocusRequester
import androidx.compose.ui.focus.focusRequester
import androidx.compose.ui.focus.onFocusChanged
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.res.stringResource
import androidx.compose.ui.text.input.ImeAction
import androidx.compose.ui.text.input.KeyboardType
import androidx.compose.ui.text.input.TextFieldValue
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.ui.app.R
import com.alexvanyo.composelife.ui.app.component.LabeledSlider
import com.alexvanyo.composelife.ui.app.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.app.theme.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.ThemePreviews
import kotlin.math.log2
import kotlin.math.pow
import kotlin.math.roundToInt

@Suppress("LongParameterList")
@Composable
fun InlineSpeedScreen(
    targetStepsPerSecond: Double,
    setTargetStepsPerSecond: (Double) -> Unit,
    generationsPerStep: Int,
    setGenerationsPerStep: (Int) -> Unit,
    modifier: Modifier = Modifier,
    scrollState: ScrollState = rememberScrollState(),
) {
    Column(
        modifier = modifier
            .verticalScroll(scrollState)
            .padding(vertical = 8.dp),
    ) {
        TargetStepsPerSecondControl(
            targetStepsPerSecond = targetStepsPerSecond,
            setTargetStepsPerSecond = setTargetStepsPerSecond,
            modifier = Modifier.padding(horizontal = 16.dp),
        )

        GenerationsPerStepControl(
            generationsPerStep = generationsPerStep,
            setGenerationsPerStep = setGenerationsPerStep,
            modifier = Modifier.padding(horizontal = 16.dp),
        )
    }
}

@OptIn(ExperimentalMaterial3Api::class)
@Suppress("LongMethod")
@Composable
fun TargetStepsPerSecondControl(
    targetStepsPerSecond: Double,
    setTargetStepsPerSecond: (Double) -> Unit,
    modifier: Modifier = Modifier,
    minTargetStepsPerSecondPowerOfTwo: Int = 0,
    maxTargetStepsPerSecondPowerOfTwo: Int = 8,
) {
    var isTextEditing by rememberSaveable { mutableStateOf(false) }
    val generationsPerStepValue = stringResource(id = R.string.target_steps_per_second_value, targetStepsPerSecond)
    var transientTextFieldValue by rememberSaveable(
        isTextEditing,
        targetStepsPerSecond,
        stateSaver = TextFieldValue.Saver,
    ) {
        mutableStateOf(TextFieldValue(generationsPerStepValue))
    }

    val transientTargetStepsPerSecond = transientTextFieldValue.text.toDoubleOrNull()
        ?.takeIf { it in 2.0.pow(minTargetStepsPerSecondPowerOfTwo)..2.0.pow(maxTargetStepsPerSecondPowerOfTwo) }

    val currentTargetStepsPerSecond = transientTargetStepsPerSecond ?: targetStepsPerSecond
    val sliderFocusRequester = remember { FocusRequester() }
    val textFieldFocusRequester = remember { FocusRequester() }

    LabeledSlider(
        label = stringResource(id = R.string.target_steps_per_second_label_and_value, currentTargetStepsPerSecond),
        value = log2(currentTargetStepsPerSecond).toFloat(),
        onValueChange = {
            setTargetStepsPerSecond(2.0.pow(it.toDouble()))
        },
        valueRange = minTargetStepsPerSecondPowerOfTwo.toFloat()..maxTargetStepsPerSecondPowerOfTwo.toFloat(),
        modifier = modifier.focusRequester(sliderFocusRequester).focusable(),
        labelSlot = {
            TextField(
                value = transientTextFieldValue,
                onValueChange = {
                    transientTextFieldValue = it
                },
                modifier = Modifier
                    .fillMaxWidth()
                    .focusRequester(textFieldFocusRequester)
                    .onFocusChanged {
                        isTextEditing = !it.isFocused
                        if (!it.isFocused && transientTargetStepsPerSecond != null) {
                            setTargetStepsPerSecond(transientTargetStepsPerSecond)
                        }
                    },
                label = {
                    Text(stringResource(id = R.string.target_steps_per_second_label))
                },
                placeholder = {
                    Text(generationsPerStepValue)
                },
                isError = transientTargetStepsPerSecond == null,
                keyboardOptions = KeyboardOptions(
                    keyboardType = KeyboardType.Decimal,
                    imeAction = ImeAction.Done,
                ),
                keyboardActions = KeyboardActions(
                    onDone = {
                        sliderFocusRequester.requestFocus()
                    }
                )
            )
        },
        sliderOverlay = {
            val tickColor = MaterialTheme.colorScheme.onSurfaceVariant

            Canvas(
                modifier = Modifier.fillMaxSize(),
            ) {
                val offsets = (minTargetStepsPerSecondPowerOfTwo..maxTargetStepsPerSecondPowerOfTwo).map {
                    (2f.pow(it) - 2f.pow(minTargetStepsPerSecondPowerOfTwo)) /
                        (2f.pow(maxTargetStepsPerSecondPowerOfTwo) - 2f.pow(minTargetStepsPerSecondPowerOfTwo))
                }

                offsets.forEach { xOffset ->
                    drawLine(
                        tickColor,
                        Offset(size.width * xOffset, 0f),
                        Offset(size.width * xOffset, size.height),
                    )
                }
            }
        },
    )
}

@OptIn(ExperimentalMaterial3Api::class)
@Suppress("LongMethod")
@Composable
fun GenerationsPerStepControl(
    generationsPerStep: Int,
    setGenerationsPerStep: (Int) -> Unit,
    modifier: Modifier = Modifier,
    minTargetStepsPerSecondPowerOfTwo: Int = 0,
    maxTargetStepsPerSecondPowerOfTwo: Int = 8,
) {
    var isTextEditing by rememberSaveable { mutableStateOf(false) }
    val generationsPerStepValue = stringResource(id = R.string.generations_per_step_value, generationsPerStep)
    var transientTextFieldValue by rememberSaveable(
        isTextEditing,
        generationsPerStep,
        stateSaver = TextFieldValue.Saver,
    ) {
        mutableStateOf(TextFieldValue(generationsPerStepValue))
    }

    val transientGenerationsPerStep = transientTextFieldValue.text.toIntOrNull()
        ?.takeIf {
            it in 2.0.pow(minTargetStepsPerSecondPowerOfTwo).toInt()..2.0.pow(maxTargetStepsPerSecondPowerOfTwo).toInt()
        }

    val currentGenerationsPerStep = transientGenerationsPerStep ?: generationsPerStep
    val sliderFocusRequester = remember { FocusRequester() }
    val textFieldFocusRequester = remember { FocusRequester() }

    LabeledSlider(
        label = stringResource(id = R.string.generations_per_step_label_and_value, currentGenerationsPerStep),
        value = log2(currentGenerationsPerStep.toFloat()),
        valueRange = minTargetStepsPerSecondPowerOfTwo.toFloat()..maxTargetStepsPerSecondPowerOfTwo.toFloat(),
        steps = maxTargetStepsPerSecondPowerOfTwo - minTargetStepsPerSecondPowerOfTwo - 1,
        onValueChange = {
            setGenerationsPerStep(2.0.pow(it.toDouble()).roundToInt())
        },
        onValueChangeFinished = {
            setGenerationsPerStep(2.0.pow(log2(generationsPerStep.toDouble()).roundToInt()).roundToInt())
        },
        modifier = modifier.focusRequester(sliderFocusRequester).focusable(),
        labelSlot = {
            TextField(
                value = transientTextFieldValue,
                onValueChange = {
                    transientTextFieldValue = it
                },
                modifier = Modifier
                    .fillMaxWidth()
                    .focusRequester(textFieldFocusRequester)
                    .onFocusChanged {
                        isTextEditing = !it.isFocused
                        if (!it.isFocused && transientGenerationsPerStep != null) {
                            setGenerationsPerStep(transientGenerationsPerStep)
                        }
                    },
                label = {
                    Text(stringResource(id = R.string.generations_per_step_label))
                },
                placeholder = {
                    Text(generationsPerStepValue)
                },
                isError = transientGenerationsPerStep == null,
                keyboardOptions = KeyboardOptions(
                    keyboardType = KeyboardType.Number,
                    imeAction = ImeAction.Done,
                ),
                keyboardActions = KeyboardActions(
                    onDone = {
                        sliderFocusRequester.requestFocus()
                    }
                )
            )
        },
    )
}

@ThemePreviews
@Composable
fun InlineSpeedScreenPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            Surface {
                InlineSpeedScreen(
                    targetStepsPerSecond = 60.0,
                    setTargetStepsPerSecond = {},
                    generationsPerStep = 1,
                    setGenerationsPerStep = {},
                )
            }
        }
    }
}
