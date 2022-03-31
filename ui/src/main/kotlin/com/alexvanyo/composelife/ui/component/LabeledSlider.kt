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

package com.alexvanyo.composelife.ui.component

import androidx.compose.foundation.interaction.MutableInteractionSource
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.layout.height
import androidx.compose.foundation.layout.padding
import androidx.compose.foundation.progressSemantics
import androidx.compose.material3.Slider
import androidx.compose.material3.SliderColors
import androidx.compose.material3.SliderDefaults
import androidx.compose.material3.Text
import androidx.compose.runtime.Composable
import androidx.compose.runtime.remember
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.semantics.clearAndSetSemantics
import androidx.compose.ui.semantics.contentDescription
import androidx.compose.ui.semantics.setProgress
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.ui.util.lerp
import kotlin.math.abs

/**
 * A wrapper around [Slider] to label it with the given [label].
 */
@Suppress("LongParameterList", "LongMethod")
@Composable
fun LabeledSlider(
    label: String,
    value: Float,
    onValueChange: (Float) -> Unit,
    modifier: Modifier = Modifier,
    enabled: Boolean = true,
    valueRange: ClosedFloatingPointRange<Float> = 0f..1f,
    steps: Int = 0,
    onValueChangeFinished: (() -> Unit)? = null,
    interactionSource: MutableInteractionSource = remember { MutableInteractionSource() },
    colors: SliderColors = SliderDefaults.colors(),
    labelSlot: @Composable () -> Unit = {
        Text(text = label, Modifier.fillMaxWidth())
    },
    sliderOverlay: @Composable () -> Unit = {},
) {
    val tickFractions = remember(steps) {
        stepsToTickFractions(steps)
    }

    Column(
        modifier = modifier
            .progressSemantics(
                value = value,
                valueRange = valueRange,
                steps = steps,
            )
            .clearAndSetSemantics {
                contentDescription = label
                setProgress(label) { targetValue ->
                    val newValue = targetValue.coerceIn(valueRange.start, valueRange.endInclusive)
                    val resolvedValue = if (steps > 0) {
                        tickFractions
                            .map {
                                lerp(
                                    valueRange.start,
                                    valueRange.endInclusive,
                                    it,
                                )
                            }
                            .minByOrNull { abs(it - newValue) } ?: newValue
                    } else {
                        newValue
                    }
                    // This is to keep it consistent with AbsSeekbar.java: return false if no
                    // change from current.
                    if (resolvedValue == value) {
                        false
                    } else {
                        onValueChange(resolvedValue)
                        true
                    }
                }
            },
    ) {
        labelSlot()

        Box(
            contentAlignment = Alignment.Center,
        ) {
            Slider(
                value = value,
                onValueChange = onValueChange,
                enabled = enabled,
                valueRange = valueRange,
                steps = steps,
                onValueChangeFinished = onValueChangeFinished,
                interactionSource = interactionSource,
                colors = colors,
            )

            Box(
                modifier = Modifier
                    .padding(horizontal = 10.dp)
                    .fillMaxWidth()
                    .height(24.dp),
            ) {
                sliderOverlay()
            }
        }
    }
}

private fun stepsToTickFractions(steps: Int): List<Float> =
    if (steps == 0) emptyList() else List(steps + 2) { it.toFloat() / (steps + 1) }
