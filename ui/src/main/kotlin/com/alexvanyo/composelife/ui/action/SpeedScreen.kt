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

package com.alexvanyo.composelife.ui.action

import androidx.compose.foundation.Canvas
import androidx.compose.foundation.ScrollState
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.layout.height
import androidx.compose.foundation.layout.padding
import androidx.compose.foundation.rememberScrollState
import androidx.compose.foundation.verticalScroll
import androidx.compose.material3.MaterialTheme
import androidx.compose.material3.Slider
import androidx.compose.material3.Text
import androidx.compose.runtime.Composable
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.res.stringResource
import androidx.compose.ui.semantics.semantics
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.ui.R
import kotlin.math.log2
import kotlin.math.pow
import kotlin.math.roundToInt

@Suppress("LongParameterList")
@Composable
fun SpeedScreen(
    targetStepsPerSecond: Double,
    setTargetStepsPerSecond: (Double) -> Unit,
    generationsPerStep: Int,
    setGenerationsPerStep: (Int) -> Unit,
    modifier: Modifier = Modifier,
    scrollState: ScrollState = rememberScrollState(),
) {
    Column(
        modifier = modifier.verticalScroll(scrollState)
    ) {
        TargetStepsPerSecondControl(
            targetStepsPerSecond = targetStepsPerSecond,
            setTargetStepsPerSecond = setTargetStepsPerSecond,
            modifier = Modifier.padding(horizontal = 16.dp)
        )

        GenerationsPerStepControl(
            generationsPerStep = generationsPerStep,
            setGenerationsPerStep = setGenerationsPerStep,
            modifier = Modifier.padding(horizontal = 16.dp)
        )
    }
}

@Composable
fun TargetStepsPerSecondControl(
    targetStepsPerSecond: Double,
    setTargetStepsPerSecond: (Double) -> Unit,
    modifier: Modifier = Modifier,
    minTargetStepsPerSecondPowerOfTwo: Int = 0,
    maxTargetStepsPerSecondPowerOfTwo: Int = 8
) {
    Column(modifier = modifier.semantics(mergeDescendants = true) {}) {
        Text(
            stringResource(id = R.string.target_steps_per_second, targetStepsPerSecond),
            modifier = Modifier.fillMaxWidth()
        )

        Box(
            contentAlignment = Alignment.Center
        ) {
            Slider(
                value = log2(targetStepsPerSecond).toFloat(),
                valueRange = minTargetStepsPerSecondPowerOfTwo.toFloat()..maxTargetStepsPerSecondPowerOfTwo.toFloat(),
                onValueChange = {
                    setTargetStepsPerSecond(2.0.pow(it.toDouble()))
                }
            )

            val tickColor = MaterialTheme.colorScheme.onSurfaceVariant

            Canvas(
                modifier = Modifier
                    .padding(horizontal = 10.dp)
                    .fillMaxWidth()
                    .height(24.dp)
            ) {
                val offsets = (minTargetStepsPerSecondPowerOfTwo..maxTargetStepsPerSecondPowerOfTwo).map {
                    (2f.pow(it) - 2f.pow(minTargetStepsPerSecondPowerOfTwo)) /
                        (2f.pow(maxTargetStepsPerSecondPowerOfTwo) - 2f.pow(minTargetStepsPerSecondPowerOfTwo))
                }

                offsets.forEach { xOffset ->
                    drawLine(
                        tickColor,
                        Offset(size.width * xOffset, 0f),
                        Offset(size.width * xOffset, size.height)
                    )
                }
            }
        }
    }
}

@Composable
fun GenerationsPerStepControl(
    generationsPerStep: Int,
    setGenerationsPerStep: (Int) -> Unit,
    modifier: Modifier = Modifier,
    minTargetStepsPerSecondPowerOfTwo: Int = 0,
    maxTargetStepsPerSecondPowerOfTwo: Int = 8
) {
    Column(modifier.semantics(mergeDescendants = true) {}) {
        Text(
            stringResource(id = R.string.generations_per_step, generationsPerStep),
            modifier = Modifier.fillMaxWidth()
        )

        Slider(
            value = log2(generationsPerStep.toFloat()),
            valueRange = minTargetStepsPerSecondPowerOfTwo.toFloat()..maxTargetStepsPerSecondPowerOfTwo.toFloat(),
            steps = maxTargetStepsPerSecondPowerOfTwo - minTargetStepsPerSecondPowerOfTwo - 1,
            onValueChange = {
                setGenerationsPerStep(2.0.pow(it.toDouble()).roundToInt())
            },
            onValueChangeFinished = {
                setGenerationsPerStep(2.0.pow(log2(generationsPerStep.toDouble()).roundToInt()).roundToInt())
            }
        )
    }
}
