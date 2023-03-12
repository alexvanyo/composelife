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

package com.alexvanyo.composelife.ui.app.component

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
import androidx.compose.ui.util.lerp
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
    sliderBijection: SliderBijection<Float> = Float.IdentitySliderBijection,
    steps: Int = 0,
    onValueChangeFinished: (() -> Unit)? = null,
    interactionSource: MutableInteractionSource = remember { MutableInteractionSource() },
    colors: SliderColors = SliderDefaults.colors(),
    labelSlot: @Composable () -> Unit = {
        Text(text = label, Modifier.fillMaxWidth())
    },
    sliderOverlay: @Composable () -> Unit = {},
) = LabeledSlider<Float>(
    label = label,
    value = value,
    onValueChange = onValueChange,
    modifier = modifier,
    enabled = enabled,
    valueRange = valueRange,
    sliderBijection = sliderBijection,
    steps = steps,
    onValueChangeFinished = onValueChangeFinished,
    interactionSource = interactionSource,
    colors = colors,
    labelSlot = labelSlot,
    sliderOverlay = sliderOverlay,
)

/**
 * A wrapper around [Slider] to label it with the given [label].
 *
 * This overload allows using a comparable [T], with a [sliderBijection] to map the values in space [T] to the
 * underlying floating-point range and steps represented by the slider.
 */
@Suppress("LongParameterList", "LongMethod")
@Composable
fun <T : Comparable<T>> LabeledSlider(
    label: String,
    value: T,
    onValueChange: (T) -> Unit,
    valueRange: ClosedRange<T>,
    sliderBijection: SliderBijection<T>,
    modifier: Modifier = Modifier,
    enabled: Boolean = true,
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
    val sliderValue = with(sliderBijection) { value.toSlider() }
    val sliderValueRange = with(sliderBijection) { valueRange.toSlider() }

    Column(
        modifier = modifier,
    ) {
        labelSlot()

        Box(
            contentAlignment = Alignment.Center,
            modifier = Modifier
                .progressSemantics(
                    value = sliderValue,
                    valueRange = sliderValueRange,
                    steps = steps,
                )
                .clearAndSetSemantics {
                    contentDescription = label
                    setProgress(label) { targetValue ->
                        val newValue = targetValue.coerceIn(sliderValueRange.start, sliderValueRange.endInclusive)
                        val resolvedValue = if (steps > 0) {
                            tickFractions
                                .map {
                                    lerp(
                                        sliderValueRange.start,
                                        sliderValueRange.endInclusive,
                                        it,
                                    )
                                }
                                .minByOrNull { abs(it - newValue) } ?: newValue
                        } else {
                            newValue
                        }
                        // This is to keep it consistent with AbsSeekbar.java: return false if no
                        // change from current.
                        if (resolvedValue == sliderValue) {
                            false
                        } else {
                            with(sliderBijection) {
                                onValueChange(resolvedValue.toValue())
                            }
                            true
                        }
                    }
                },
        ) {
            Slider(
                value = sliderValue,
                onValueChange = {
                    onValueChange(with(sliderBijection) { it.toValue() })
                },
                enabled = enabled,
                valueRange = sliderValueRange,
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

/**
 * A bijection between the space of [T] and the floating point space for a slider.
 */
interface SliderBijection<T : Comparable<T>> {
    fun valueToSlider(value: T): Float
    fun sliderToValue(sliderValue: Float): T
}

/**
 * The identity bijection for a type of [Float].
 */
val Float.Companion.IdentitySliderBijection get(): SliderBijection<Float> = object : SliderBijection<Float> {
    override fun valueToSlider(value: Float): Float = value
    override fun sliderToValue(sliderValue: Float): Float = sliderValue
}

/**
 * Converts the value [T] into the slider [Float] space using the [SliderBijection].
 */
context(SliderBijection<T>)
fun <T : Comparable<T>> T.toSlider(): Float = valueToSlider(this)

/**
 * Converts the value in the slider [Float] space into the type [T] using the [SliderBijection].
 */
context(SliderBijection<T>)
fun <T : Comparable<T>> Float.toValue(): T = sliderToValue(this)

/**
 * Converts the [ClosedRange] of type [T] into a [ClosedFloatingPointRange] in the slider [Float] space using the
 * [SliderBijection].
 */
context(SliderBijection<T>)
fun <T : Comparable<T>> ClosedRange<T>.toSlider(): ClosedFloatingPointRange<Float> =
    valueToSlider(start)..valueToSlider(endInclusive)

/**
 * Converts the [ClosedFloatingPointRange] in the slider [Float] space into a [ClosedRange] of type [T] using the
 * [SliderBijection].
 */
context(SliderBijection<T>)
fun <T : Comparable<T>> ClosedFloatingPointRange<Float>.toValue(): ClosedRange<T> =
    sliderToValue(start)..sliderToValue(endInclusive)

private fun stepsToTickFractions(steps: Int): List<Float> =
    if (steps == 0) emptyList() else List(steps + 2) { it.toFloat() / (steps + 1) }
