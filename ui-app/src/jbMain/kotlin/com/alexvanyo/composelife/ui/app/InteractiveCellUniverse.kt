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
@file:Suppress("MatchingDeclarationName")

package com.alexvanyo.composelife.ui.app

import androidx.compose.foundation.focusable
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.setValue
import androidx.compose.ui.Modifier
import androidx.compose.ui.focus.FocusRequester
import androidx.compose.ui.focus.focusRequester
import androidx.compose.ui.focus.onFocusChanged
import androidx.compose.ui.input.key.Key
import androidx.compose.ui.input.key.KeyEventType
import androidx.compose.ui.input.key.isCtrlPressed
import androidx.compose.ui.input.key.key
import androidx.compose.ui.input.key.onKeyEvent
import androidx.compose.ui.input.key.type
import androidx.compose.ui.platform.testTag
import androidx.window.core.layout.WindowSizeClass
import com.alexvanyo.composelife.model.DeserializationResult
import com.alexvanyo.composelife.model.TemporalGameOfLifeState
import com.alexvanyo.composelife.model.isRunning
import com.alexvanyo.composelife.sessionvalue.SessionValue
import com.alexvanyo.composelife.ui.cells.MutableCellWindow
import com.alexvanyo.composelife.ui.cells.SelectionState
import com.alexvanyo.composelife.ui.settings.Setting
import com.alexvanyo.composelife.ui.util.ImmersiveModeManager
import kotlin.uuid.Uuid

/**
 * An interactive cell universe displaying the given [temporalGameOfLifeState] and the controls for adjusting how it
 * evolves.
 */
context(InteractiveCellUniverseInjectEntryPoint, InteractiveCellUniverseLocalEntryPoint)
@Suppress("LongParameterList", "LongMethod", "CyclomaticComplexMethod")
@Composable
fun InteractiveCellUniverse(
    temporalGameOfLifeState: TemporalGameOfLifeState,
    immersiveModeManager: ImmersiveModeManager,
    windowSizeClass: WindowSizeClass,
    onSeeMoreSettingsClicked: () -> Unit,
    onOpenInSettingsClicked: (setting: Setting) -> Unit,
    onViewDeserializationInfo: (DeserializationResult) -> Unit,
    modifier: Modifier = Modifier,
    interactiveCellUniverseState: InteractiveCellUniverseState =
        rememberInteractiveCellUniverseState(temporalGameOfLifeState, immersiveModeManager),
) {
    // Force focus to allow listening to key events
    var hasFocus by remember { mutableStateOf(false) }
    val focusRequester = remember { FocusRequester() }
    if (!hasFocus) {
        LaunchedEffect(Unit) {
            focusRequester.requestFocus()
        }
    }

    Box(
        modifier = modifier
            .fillMaxSize()
            .focusRequester(focusRequester)
            .onFocusChanged {
                hasFocus = it.hasFocus
            }
            .focusable()
            .onKeyEvent { keyEvent ->
                when (keyEvent.type) {
                    KeyEventType.KeyDown -> {
                        when (keyEvent.key) {
                            Key.Spacebar -> {
                                temporalGameOfLifeState.setIsRunning(!temporalGameOfLifeState.isRunning)
                                true
                            }

                            Key.A -> if (keyEvent.isCtrlPressed) {
                                interactiveCellUniverseState.onSelectAll()
                                true
                            } else {
                                false
                            }

                            Key.C -> if (keyEvent.isCtrlPressed) {
                                interactiveCellUniverseState.onCopy()
                            } else {
                                false
                            }

                            Key.V -> if (keyEvent.isCtrlPressed) {
                                interactiveCellUniverseState.onPaste()
                                true
                            } else {
                                false
                            }

                            Key.X -> if (keyEvent.isCtrlPressed) {
                                interactiveCellUniverseState.onCut()
                            } else {
                                false
                            }

                            Key.Escape -> {
                                interactiveCellUniverseState.cellWindowInteractionState.selectionSessionState =
                                    SessionValue(Uuid.random(), Uuid.random(), SelectionState.NoSelection)
                                true
                            }

                            else -> false
                        }
                    }

                    else -> false
                }
            },
    ) {
        MutableCellWindow(
            gameOfLifeState = temporalGameOfLifeState,
            modifier = Modifier.testTag("MutableCellWindow"),
            cellWindowInteractionState = interactiveCellUniverseState.cellWindowInteractionState,
        )

        InteractiveCellUniverseOverlay(
            temporalGameOfLifeState = temporalGameOfLifeState,
            interactiveCellUniverseState = interactiveCellUniverseState,
            cellWindowViewportState = interactiveCellUniverseState.mutableCellWindowViewportState,
            windowSizeClass = windowSizeClass,
            onSeeMoreSettingsClicked = onSeeMoreSettingsClicked,
            onOpenInSettingsClicked = onOpenInSettingsClicked,
            onViewDeserializationInfo = onViewDeserializationInfo,
        )
    }
}
