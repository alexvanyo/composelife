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
import androidx.compose.material3.windowsizeclass.WindowSizeClass
import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.setValue
import androidx.compose.ui.ExperimentalComposeUiApi
import androidx.compose.ui.Modifier
import androidx.compose.ui.focus.FocusRequester
import androidx.compose.ui.focus.focusRequester
import androidx.compose.ui.focus.onFocusChanged
import androidx.compose.ui.input.key.Key
import androidx.compose.ui.input.key.KeyEventType
import androidx.compose.ui.input.key.key
import androidx.compose.ui.input.key.onKeyEvent
import androidx.compose.ui.input.key.type
import androidx.compose.ui.platform.testTag
import com.alexvanyo.composelife.model.TemporalGameOfLifeState
import com.alexvanyo.composelife.model.isRunning
import com.alexvanyo.composelife.ui.app.cells.CellWindowLocalEntryPoint
import com.alexvanyo.composelife.ui.app.cells.MutableCellWindow
import com.alexvanyo.composelife.ui.app.cells.MutableCellWindowState
import com.alexvanyo.composelife.ui.app.cells.TrackingCellWindowState
import com.alexvanyo.composelife.ui.app.cells.ViewportInteractionConfig
import com.alexvanyo.composelife.ui.app.cells.rememberMutableCellWindowState
import com.alexvanyo.composelife.ui.app.cells.rememberTrackingCellWindowState
import dagger.hilt.EntryPoint
import dagger.hilt.InstallIn
import dagger.hilt.android.components.ActivityComponent

@EntryPoint
@InstallIn(ActivityComponent::class)
interface InteractiveCellUniverseHiltEntryPoint :
    InteractiveCellUniverseOverlayHiltEntryPoint

interface InteractiveCellUniverseLocalEntryPoint :
    CellWindowLocalEntryPoint,
    InteractiveCellUniverseOverlayLocalEntryPoint

/**
 * An interactive cell universe displaying the given [temporalGameOfLifeState] and the controls for adjusting how it
 * evolves.
 */
context(InteractiveCellUniverseHiltEntryPoint, InteractiveCellUniverseLocalEntryPoint)
@OptIn(ExperimentalComposeUiApi::class)
@Suppress("LongParameterList")
@Composable
fun InteractiveCellUniverse(
    temporalGameOfLifeState: TemporalGameOfLifeState,
    isViewportTracking: Boolean,
    setIsViewportTracking: (Boolean) -> Unit,
    windowSizeClass: WindowSizeClass,
    modifier: Modifier = Modifier,
    mutableCellWindowState: MutableCellWindowState = rememberMutableCellWindowState(),
    trackingCellWindowState: TrackingCellWindowState = rememberTrackingCellWindowState(temporalGameOfLifeState),
) {
    val viewportInteractionConfig = remember(isViewportTracking, mutableCellWindowState, trackingCellWindowState) {
        if (isViewportTracking) {
            ViewportInteractionConfig.Tracking(
                trackingCellWindowState = trackingCellWindowState,
                syncableMutableCellWindowStates = listOf(mutableCellWindowState),
            )
        } else {
            ViewportInteractionConfig.Navigable(
                mutableCellWindowState = mutableCellWindowState,
            )
        }
    }

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
                if (keyEvent.key == Key.Spacebar && keyEvent.type == KeyEventType.KeyUp) {
                    temporalGameOfLifeState.setIsRunning(!temporalGameOfLifeState.isRunning)
                    true
                } else {
                    false
                }
            }
    ) {
        MutableCellWindow(
            gameOfLifeState = temporalGameOfLifeState,
            modifier = Modifier.testTag("MutableCellWindow"),
            viewportInteractionConfig = viewportInteractionConfig,
        )

        InteractiveCellUniverseOverlay(
            temporalGameOfLifeState = temporalGameOfLifeState,
            cellWindowState = mutableCellWindowState,
            isViewportTracking = isViewportTracking,
            setIsViewportTracking = setIsViewportTracking,
            windowSizeClass = windowSizeClass,
        )
    }
}
