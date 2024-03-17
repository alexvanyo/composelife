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
import com.alexvanyo.composelife.sessionvaluekey.SessionValue
import com.alexvanyo.composelife.sessionvaluekey.UpgradableSessionKey
import java.util.UUID

@Suppress("LongParameterList", "LongMethod")
@Composable
fun <T : Comparable<T>> EditableSlider(
    labelAndValueText: @Composable (T) -> String,
    valueText: (T) -> String,
    labelText: String,
    textToValue: (String) -> T?,
    sessionValue: SessionValue<T>,
    onSessionValueChange: (SessionValue<T>) -> Unit,
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
    val value = sessionValue.value

    /**
     * The [String] representation of the [value] passed in.
     */
    val nonTransientValueText = valueText(value)

    val oldSessionId = sessionValue.sessionId
    val nextSessionId = remember(oldSessionId) { UUID.randomUUID() }
    val upgradableSessionKey = UpgradableSessionKey(
        a = oldSessionId,
        b = nextSessionId,
    )
    val currentSessionId = remember(upgradableSessionKey) { nextSessionId }

    /**
     * The transient [TextField] value that the user is editing.
     */
    var transientTextFieldValue by key(currentSessionId) {
        rememberSaveable { mutableStateOf(nonTransientValueText) }
    }

    /**
     * Parses a value [T] from the given [text].
     */
    fun parseValue(text: String): T? =
        textToValue(text)?.coerceIn(valueRange)

    /**
     * If non-null, this is the value [T] created from the currently entered string in the current edit session, as
     * stored in [transientTextFieldValue].
     *
     * If null, the currently entered string cannot be turned into a value of type [T].
     */
    val transientValue = parseValue(transientTextFieldValue)

    /**
     * The current value to display. This is either the current transient value, or the persisted [value] if the
     * transient value is `null`.
     */
    val currentValue = transientValue ?: value

    val sliderFocusRequester = remember { FocusRequester() }
    val textFieldFocusRequester = remember { FocusRequester() }

    LabeledSlider(
        label = labelAndValueText(currentValue),
        value = currentValue,
        onValueChange = {
            onSessionValueChange(SessionValue(UUID.randomUUID(), UUID.randomUUID(), it))
        },
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
            /**
             * True if this is the first invocation of [onFocusChanged].
             */
            var isFirstFocusedChanged: Boolean by remember { mutableStateOf(true) }

            TextField(
                value = transientTextFieldValue,
                onValueChange = { value ->
                    // Update the text field value
                    transientTextFieldValue = value
                    // Try parsing the text field value into a real value
                    parseValue(value)?.let { newTransientValue ->
                        // If successful, call onValueChange with the new transient value, and update the known
                        // transient value text we will receive by converting back to text.
                        onSessionValueChange(SessionValue(currentSessionId, UUID.randomUUID(), newTransientValue))
                    }
                },
                modifier = Modifier
                    .fillMaxWidth()
                    .focusRequester(textFieldFocusRequester)
                    .onFocusChanged {
                        if (!isFirstFocusedChanged && !it.isFocused) {
                            // If we are no longer focused, the current editing session has ended, so update the
                            // value with a randomized session id and invoke the finished listener.
                            onSessionValueChange(SessionValue(UUID.randomUUID(), UUID.randomUUID(), value))
                            onValueChangeFinished?.invoke()
                        }
                        isFirstFocusedChanged = false
                    },
                label = {
                    Text(labelText)
                },
                placeholder = {
                    Text(nonTransientValueText)
                },
                isError = transientValue == null,
                keyboardOptions = KeyboardOptions(
                    keyboardType = keyboardType,
                    imeAction = ImeAction.Done,
                ),
                keyboardActions = KeyboardActions(
                    onDone = {
                        // Move focus to the overall slider to remove it from the TextField
                        sliderFocusRequester.requestFocus()
                    },
                ),
                singleLine = true,
            )
        },
        sliderOverlay = sliderOverlay,
    )
}
