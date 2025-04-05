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

package com.alexvanyo.composelife.ui.mobile.component

import androidx.compose.foundation.focusable
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.text.KeyboardOptions
import androidx.compose.foundation.text.input.InputTransformation
import androidx.compose.foundation.text.input.TextFieldLineLimits
import androidx.compose.foundation.text.input.TextFieldState
import androidx.compose.foundation.text.input.rememberTextFieldState
import androidx.compose.material3.SliderColors
import androidx.compose.material3.SliderDefaults
import androidx.compose.material3.Text
import androidx.compose.material3.TextField
import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.Stable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.runtime.setValue
import androidx.compose.runtime.snapshotFlow
import androidx.compose.ui.Modifier
import androidx.compose.ui.focus.FocusRequester
import androidx.compose.ui.focus.FocusState
import androidx.compose.ui.focus.focusRequester
import androidx.compose.ui.focus.onFocusChanged
import androidx.compose.ui.text.input.ImeAction
import com.alexvanyo.composelife.sessionvalue.SessionValue
import com.alexvanyo.composelife.sessionvalue.localSessionId
import com.alexvanyo.composelife.sessionvalue.rememberSessionValueHolder
import com.alexvanyo.composelife.ui.util.nonNegativeDouble
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.flow.buffer
import kotlinx.coroutines.flow.filterNotNull
import kotlinx.serialization.KSerializer
import kotlinx.serialization.serializer
import kotlin.uuid.Uuid

@Suppress("LongParameterList")
@Composable
inline fun <reified T : Comparable<T>> EditableSlider(
    noinline labelAndValueText: @Composable (T) -> String,
    noinline valueText: (T) -> String,
    labelText: String,
    noinline textToValue: (String) -> T?,
    sessionValue: SessionValue<T>,
    noinline onSessionValueChange: (expected: SessionValue<T>, newValue: SessionValue<T>) -> Unit,
    valueRange: ClosedRange<T>,
    sliderBijection: SliderBijection<T>,
    modifier: Modifier = Modifier,
    enabled: Boolean = true,
    steps: Int = 0,
    noinline onValueChangeFinished: (() -> Unit)? = null,
    colors: SliderColors = SliderDefaults.colors(),
    noinline sliderOverlay: @Composable () -> Unit = {},
    noinline prefix: (@Composable () -> Unit)? = null,
    noinline suffix: (@Composable () -> Unit)? = null,
    noinline supportingText: (@Composable () -> Unit)? = null,
    inputTransformation: InputTransformation = InputTransformation.nonNegativeDouble(),
) = EditableSlider(
    labelAndValueText = labelAndValueText,
    valueText = valueText,
    labelText = labelText,
    textToValue = textToValue,
    sessionValue = sessionValue,
    onSessionValueChange = onSessionValueChange,
    valueRange = valueRange,
    sliderBijection = sliderBijection,
    valueSerializer = serializer(),
    modifier = modifier,
    enabled = enabled,
    steps = steps,
    onValueChangeFinished = onValueChangeFinished,
    colors = colors,
    sliderOverlay = sliderOverlay,
    prefix = prefix,
    suffix = suffix,
    supportingText = supportingText,
    inputTransformation = inputTransformation,
)

@Suppress("LongParameterList")
@Composable
fun <T : Comparable<T>> EditableSlider(
    labelAndValueText: @Composable (T) -> String,
    valueText: (T) -> String,
    labelText: String,
    textToValue: (String) -> T?,
    sessionValue: SessionValue<T>,
    onSessionValueChange: (expected: SessionValue<T>, newValue: SessionValue<T>) -> Unit,
    valueRange: ClosedRange<T>,
    sliderBijection: SliderBijection<T>,
    valueSerializer: KSerializer<T>,
    modifier: Modifier = Modifier,
    enabled: Boolean = true,
    steps: Int = 0,
    onValueChangeFinished: (() -> Unit)? = null,
    colors: SliderColors = SliderDefaults.colors(),
    sliderOverlay: @Composable () -> Unit = {},
    prefix: (@Composable () -> Unit)? = null,
    suffix: (@Composable () -> Unit)? = null,
    supportingText: (@Composable () -> Unit)? = null,
    inputTransformation: InputTransformation = InputTransformation.nonNegativeDouble(),
) {
    val state = rememberEditableSliderState(
        labelAndValueText = labelAndValueText,
        valueText = valueText,
        textToValue = textToValue,
        sessionValue = sessionValue,
        onSessionValueChange = onSessionValueChange,
        valueRange = valueRange,
        onValueChangeFinished = onValueChangeFinished,
        valueSerializer = valueSerializer,
    )

    val sliderFocusRequester = remember { FocusRequester() }
    val textFieldFocusRequester = remember { FocusRequester() }

    LabeledSlider(
        label = state.sliderLabel,
        value = state.currentValue,
        onValueChange = state::onSliderValueChange,
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
                state = state.textFieldState,
                modifier = Modifier
                    .fillMaxWidth()
                    .focusRequester(textFieldFocusRequester)
                    .onFocusChanged(state::onTextFieldFocusChanged),
                label = {
                    Text(labelText)
                },
                placeholder = {
                    Text(state.placeholderText)
                },
                prefix = prefix,
                suffix = suffix,
                supportingText = supportingText,
                isError = state.isError,
                keyboardOptions = KeyboardOptions(
                    imeAction = ImeAction.Done,
                ),
                inputTransformation = inputTransformation,
                onKeyboardAction = { performDefaultAction ->
                    performDefaultAction()
                    sliderFocusRequester.requestFocus()
                },
                lineLimits = TextFieldLineLimits.SingleLine,
            )
        },
        sliderOverlay = sliderOverlay,
    )
}

@Suppress("LongParameterList")
@Composable
private fun <T : Comparable<T>> rememberEditableSliderState(
    labelAndValueText: @Composable (T) -> String,
    valueText: (T) -> String,
    textToValue: (String) -> T?,
    sessionValue: SessionValue<T>,
    onSessionValueChange: (expected: SessionValue<T>, newValue: SessionValue<T>) -> Unit,
    valueRange: ClosedRange<T>,
    onValueChangeFinished: (() -> Unit)?,
    valueSerializer: KSerializer<T>,
): EditableSliderState<T> {
    /**
     * True if this is the first invocation of [onFocusChanged].
     */
    var isFirstFocusedChanged: Boolean by remember { mutableStateOf(true) }

    /**
     * The [String] representation of the [value] passed in.
     */
    val nonTransientValueText = valueText(sessionValue.value)

    val textFieldSessionValueHolder = rememberSessionValueHolder(
        upstreamSessionValue = sessionValue,
        setUpstreamSessionValue = { expected, newValue -> onSessionValueChange(expected, newValue) },
        valueSerializer = valueSerializer,
    )
    /**
     * The transient [TextField] value that the user is editing.
     *
     * This resets if the local session id changes, which occurs if either the value is updated elsewhere, or
     * the editing session of the text has completed
     */
    val transientTextFieldState = key(textFieldSessionValueHolder.info.localSessionId) {
        rememberTextFieldState(
            initialText = nonTransientValueText,
        )
    }

    val editableSliderState = remember(
        labelAndValueText,
        valueText,
        textToValue,
        onSessionValueChange,
        valueRange,
        onValueChangeFinished,
        nonTransientValueText,
        textFieldSessionValueHolder,
        transientTextFieldState,
    ) {
        object : EditableSliderState<T> {
            /**
             * Parses a value [T] from the given [text].
             */
            private fun parseValue(text: String): T? =
                textToValue(text)?.coerceIn(valueRange)

            /**
             * If non-null, this is the value [T] created from the currently entered string in the current edit session,
             * as stored in [transientTextFieldState].
             *
             * If null, the currently entered string cannot be turned into a value of type [T].
             */
            val transientValue: T?
                get() = parseValue(transientTextFieldState.text.toString())

            override val currentValue: T
                get() = transientValue ?: textFieldSessionValueHolder.sessionValue.value

            override val textFieldState: TextFieldState
                get() = transientTextFieldState
            override val sliderLabel: String
                @Composable get() = labelAndValueText(currentValue)
            override val placeholderText: String
                get() = nonTransientValueText
            override val isError: Boolean
                get() = transientValue == null

            override fun onSliderValueChange(value: T) {
                onSessionValueChange(
                    textFieldSessionValueHolder.sessionValue,
                    SessionValue(Uuid.random(), Uuid.random(), value)
                )
            }

            override fun onTextFieldFocusChanged(focusState: FocusState) {
                if (!isFirstFocusedChanged && !focusState.isFocused) {
                    // If we are no longer focused, the current editing session has ended, so update the
                    // value with the current value and a randomized session id and then invoke the finished
                    // listener.
                    onSessionValueChange(
                        textFieldSessionValueHolder.sessionValue,
                        SessionValue(Uuid.random(), Uuid.random(), currentValue)
                    )
                    onValueChangeFinished?.invoke()
                }
                isFirstFocusedChanged = false
            }
        }
    }

    val currentEditableSliderState by rememberUpdatedState(editableSliderState)

    // Synchronize the transient value back to the session value holder, if it has changed
    LaunchedEffect(textFieldSessionValueHolder) {
        snapshotFlow { currentEditableSliderState.transientValue }
            .buffer(Channel.CONFLATED)
            .filterNotNull()
            .collect { newTransientValue ->
                if (textFieldSessionValueHolder.sessionValue.value != newTransientValue) {
                    textFieldSessionValueHolder.setValue(newTransientValue)
                }
            }
    }

    return currentEditableSliderState
}

@Stable
private interface EditableSliderState<T : Comparable<T>> {
    /**
     * The current value to display. This is either the current transient value, or the persisted [value] if the
     * transient value is `null`.
     */
    val currentValue: T

    /**
     * The backing [TextFieldState]
     */
    val textFieldState: TextFieldState

    /**
     * The label for the slider.
     */
    @get:Composable
    val sliderLabel: String

    /**
     * The placeholder text.
     */
    val placeholderText: String

    /**
     * True if the current value for the text field is invalid.
     */
    val isError: Boolean

    fun onSliderValueChange(value: T)
    fun onTextFieldFocusChanged(focusState: FocusState)
}
