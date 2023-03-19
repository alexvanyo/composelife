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
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.foundation.layout.padding
import androidx.compose.foundation.rememberScrollState
import androidx.compose.foundation.verticalScroll
import androidx.compose.material3.MaterialTheme
import androidx.compose.material3.Surface
import androidx.compose.runtime.Composable
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.res.stringResource
import androidx.compose.ui.text.input.KeyboardType
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResolver
import com.alexvanyo.composelife.ui.app.R
import com.alexvanyo.composelife.ui.app.component.EditableSlider
import com.alexvanyo.composelife.ui.app.component.SliderBijection
import com.alexvanyo.composelife.ui.app.component.toValue
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

private object TargetStepsPerSecondSliderBijection : SliderBijection<Double> {
    override fun valueToSlider(value: Double): Float = log2(value).toFloat()
    override fun sliderToValue(sliderValue: Float): Double = 2.0.pow(sliderValue.toDouble())
}

@Composable
fun TargetStepsPerSecondControl(
    targetStepsPerSecond: Double,
    setTargetStepsPerSecond: (Double) -> Unit,
    modifier: Modifier = Modifier,
    minTargetStepsPerSecondPowerOfTwo: Int = 0,
    maxTargetStepsPerSecondPowerOfTwo: Int = 8,
) {
    val valueRange = with(TargetStepsPerSecondSliderBijection) {
        (minTargetStepsPerSecondPowerOfTwo.toFloat()..maxTargetStepsPerSecondPowerOfTwo.toFloat()).toValue()
    }

    val resolver = parameterizedStringResolver()
    EditableSlider(
        labelAndValueText = {
            stringResource(id = R.string.target_steps_per_second_label_and_value, it)
        },
        valueText = { resolver(ParameterizedString(R.string.target_steps_per_second_value, it)) },
        labelText = stringResource(id = R.string.target_steps_per_second_label),
        textToValue = { it.toDoubleOrNull() },
        value = targetStepsPerSecond,
        onValueChange = setTargetStepsPerSecond,
        valueRange = valueRange,
        sliderBijection = TargetStepsPerSecondSliderBijection,
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
        modifier = modifier,
    )
}

private object GenerationsPerStepSliderBijection : SliderBijection<Int> {
    override fun valueToSlider(value: Int): Float = log2(value.toFloat())
    override fun sliderToValue(sliderValue: Float): Int = 2.0.pow(sliderValue.toDouble()).roundToInt()
}

@Composable
fun GenerationsPerStepControl(
    generationsPerStep: Int,
    setGenerationsPerStep: (Int) -> Unit,
    modifier: Modifier = Modifier,
    minGenerationsPerStepPowerOfTwo: Int = 0,
    maxGenerationsPerStepPowerOfTwo: Int = 8,
) {
    val valueRange = with(GenerationsPerStepSliderBijection) {
        (minGenerationsPerStepPowerOfTwo.toFloat()..maxGenerationsPerStepPowerOfTwo.toFloat()).toValue()
    }

    val resolver = parameterizedStringResolver()
    EditableSlider(
        labelAndValueText = { stringResource(id = R.string.generations_per_step_label_and_value, it) },
        valueText = { resolver(ParameterizedString(R.string.generations_per_step_value, it)) },
        labelText = stringResource(id = R.string.generations_per_step_label),
        textToValue = { it.toIntOrNull() },
        value = generationsPerStep,
        valueRange = valueRange,
        sliderBijection = GenerationsPerStepSliderBijection,
        steps = maxGenerationsPerStepPowerOfTwo - minGenerationsPerStepPowerOfTwo - 1,
        onValueChange = {
            setGenerationsPerStep(it)
        },
        keyboardType = KeyboardType.Number,
        modifier = modifier,
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
