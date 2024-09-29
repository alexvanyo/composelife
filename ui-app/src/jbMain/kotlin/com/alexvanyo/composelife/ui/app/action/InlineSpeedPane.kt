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
import androidx.compose.foundation.text.input.InputTransformation
import androidx.compose.foundation.verticalScroll
import androidx.compose.material3.MaterialTheme
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResolver
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResource
import com.alexvanyo.composelife.sessionvalue.SessionValue
import com.alexvanyo.composelife.ui.app.component.EditableSlider
import com.alexvanyo.composelife.ui.app.component.SliderBijection
import com.alexvanyo.composelife.ui.app.component.toValue
import com.alexvanyo.composelife.ui.app.resources.GenerationsPerStepLabel
import com.alexvanyo.composelife.ui.app.resources.GenerationsPerStepLabelAndValue
import com.alexvanyo.composelife.ui.app.resources.GenerationsPerStepValue
import com.alexvanyo.composelife.ui.app.resources.Strings
import com.alexvanyo.composelife.ui.app.resources.TargetStepsPerSecondLabel
import com.alexvanyo.composelife.ui.app.resources.TargetStepsPerSecondLabelAndValue
import com.alexvanyo.composelife.ui.app.resources.TargetStepsPerSecondValue
import com.alexvanyo.composelife.ui.util.nonNegativeDouble
import com.alexvanyo.composelife.ui.util.nonNegativeLong
import com.alexvanyo.composelife.ui.util.uuidSaver
import kotlin.math.log2
import kotlin.math.pow
import kotlin.math.roundToInt
import kotlin.uuid.Uuid

@Suppress("LongParameterList")
@Composable
fun InlineSpeedPane(
    targetStepsPerSecond: Double,
    setTargetStepsPerSecond: (Double) -> Unit,
    generationsPerStep: Int,
    setGenerationsPerStep: (Int) -> Unit,
    modifier: Modifier = Modifier,
    scrollState: ScrollState = rememberScrollState(initial = Int.MAX_VALUE),
) {
    Column(
        modifier = modifier
            .verticalScroll(
                state = scrollState,
                reverseScrolling = true,
            )
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

    var sessionId by rememberSaveable(stateSaver = uuidSaver) { mutableStateOf(Uuid.random()) }
    var valueId by rememberSaveable(stateSaver = uuidSaver) { mutableStateOf(Uuid.random()) }
    val resolver = parameterizedStringResolver()
    EditableSlider(
        labelAndValueText = {
            parameterizedStringResource(Strings.TargetStepsPerSecondLabelAndValue(it))
        },
        valueText = { resolver(Strings.TargetStepsPerSecondValue(it)) },
        labelText = parameterizedStringResource(Strings.TargetStepsPerSecondLabel),
        textToValue = { it.toDoubleOrNull() },
        sessionValue = SessionValue(sessionId, valueId, targetStepsPerSecond),
        onSessionValueChange = {
            sessionId = it.sessionId
            valueId = it.valueId
            setTargetStepsPerSecond(it.value)
        },
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
        inputTransformation = InputTransformation.nonNegativeDouble(),
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

    var sessionId by rememberSaveable(stateSaver = uuidSaver) { mutableStateOf(Uuid.random()) }
    var valueId by rememberSaveable(stateSaver = uuidSaver) { mutableStateOf(Uuid.random()) }

    val resolver = parameterizedStringResolver()
    EditableSlider(
        labelAndValueText = { parameterizedStringResource(Strings.GenerationsPerStepLabelAndValue(it)) },
        valueText = { resolver(Strings.GenerationsPerStepValue(it)) },
        labelText = parameterizedStringResource(Strings.GenerationsPerStepLabel),
        textToValue = { it.toIntOrNull() },
        sessionValue = SessionValue(sessionId, valueId, generationsPerStep),
        valueRange = valueRange,
        sliderBijection = GenerationsPerStepSliderBijection,
        steps = maxGenerationsPerStepPowerOfTwo - minGenerationsPerStepPowerOfTwo - 1,
        onSessionValueChange = {
            sessionId = it.sessionId
            valueId = it.valueId
            setGenerationsPerStep(it.value)
        },
        inputTransformation = InputTransformation.nonNegativeLong(),
        modifier = modifier,
    )
}
