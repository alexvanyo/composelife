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

package com.alexvanyo.composelife.ui.wear

import androidx.compose.foundation.gestures.awaitEachGesture
import androidx.compose.foundation.gestures.awaitFirstDown
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.runtime.snapshotFlow
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.draw.alpha
import androidx.compose.ui.input.pointer.pointerInput
import androidx.wear.compose.foundation.HierarchicalFocusCoordinator
import androidx.wear.compose.foundation.rememberActiveFocusRequester
import androidx.wear.compose.foundation.rotary.rotaryScrollable
import androidx.wear.compose.material3.MaterialTheme
import androidx.wear.compose.material3.Picker
import androidx.wear.compose.material3.Text
import androidx.wear.compose.material3.rememberPickerState
import com.google.android.horologist.compose.rotaryinput.accumulatedBehavior
import kotlinx.coroutines.launch

@Composable
@Suppress("LongParameterList")
fun ColorComponentPicker(
    isSelected: Boolean,
    onSelected: () -> Unit,
    initialComponentValue: Int,
    setComponentValue: (Int) -> Unit,
    contentDescription: String,
    modifier: Modifier = Modifier,
) {
    val pickerState = rememberPickerState(
        initialNumberOfOptions = 256,
        initiallySelectedOption = remember { initialComponentValue },
    )
    val currentSetComponentValue by rememberUpdatedState(setComponentValue)

    val coroutineScope = rememberCoroutineScope()

    LaunchedEffect(pickerState) {
        snapshotFlow { pickerState.selectedOption }
            .collect {
                currentSetComponentValue(it)
            }
    }

    HierarchicalFocusCoordinator(
        requiresFocus = { isSelected },
    ) {
        Picker(
            state = pickerState,
            contentDescription = contentDescription,
            onSelected = onSelected,
            modifier = modifier
                .rotaryScrollable(
                    behavior = accumulatedBehavior {
                        coroutineScope.launch {
                            pickerState.scrollToOption(pickerState.selectedOption + if (it > 0) 1 else -1)
                        }
                    },
                    focusRequester = rememberActiveFocusRequester(),
                ),
        ) { optionIndex ->
            Box(
                contentAlignment = Alignment.Center,
                modifier = Modifier
                    .fillMaxSize()
                    .pointerInput(Unit) {
                        awaitEachGesture {
                            awaitFirstDown()
                            onSelected()
                        }
                    },
            ) {
                Text(
                    text = "%02X".format(optionIndex),
                    style = MaterialTheme.typography.displayMedium,
                    modifier = Modifier.alpha(if (isSelected) 1f else 0.5f),
                )
            }
        }
    }
}
