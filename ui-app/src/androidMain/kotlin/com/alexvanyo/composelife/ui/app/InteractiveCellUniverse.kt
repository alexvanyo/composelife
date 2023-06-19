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
import androidx.compose.runtime.derivedStateOf
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
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
import com.alexvanyo.composelife.ui.app.action.CellUniverseActionCardState
import com.alexvanyo.composelife.ui.app.action.rememberCellUniverseActionCardState
import com.alexvanyo.composelife.ui.app.cells.CellWindowLocalEntryPoint
import com.alexvanyo.composelife.ui.app.cells.MutableCellWindow
import com.alexvanyo.composelife.ui.app.cells.MutableCellWindowState
import com.alexvanyo.composelife.ui.app.cells.TrackingCellWindowState
import com.alexvanyo.composelife.ui.app.cells.ViewportInteractionConfig
import com.alexvanyo.composelife.ui.app.cells.rememberMutableCellWindowState
import com.alexvanyo.composelife.ui.app.cells.rememberTrackingCellWindowState
import com.alexvanyo.composelife.ui.app.info.CellUniverseInfoCardState
import com.alexvanyo.composelife.ui.app.info.rememberCellUniverseInfoCardState
import com.alexvanyo.composelife.ui.util.PredictiveBackState
import com.alexvanyo.composelife.ui.util.TargetState
import com.alexvanyo.composelife.ui.util.predictiveBackHandler
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
@Suppress("LongParameterList")
@Composable
fun InteractiveCellUniverse(
    temporalGameOfLifeState: TemporalGameOfLifeState,
    windowSizeClass: WindowSizeClass,
    modifier: Modifier = Modifier,
    interactiveCellUniverseState: InteractiveCellUniverseState =
        rememberInteractiveCellUniverseState(temporalGameOfLifeState),
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
            .then(
                if (interactiveCellUniverseState.isOverlayShowingFullscreen) {
                    Modifier
                } else {
                    Modifier.onKeyEvent { keyEvent ->
                        if (keyEvent.key == Key.Spacebar && keyEvent.type == KeyEventType.KeyUp) {
                            temporalGameOfLifeState.setIsRunning(!temporalGameOfLifeState.isRunning)
                            true
                        } else {
                            false
                        }
                    }
                },
            ),
    ) {
        if (!interactiveCellUniverseState.isOverlayShowingFullscreen) {
            MutableCellWindow(
                gameOfLifeState = temporalGameOfLifeState,
                modifier = Modifier.testTag("MutableCellWindow"),
                viewportInteractionConfig = interactiveCellUniverseState.viewportInteractionConfig,
            )
        }

        InteractiveCellUniverseOverlay(
            temporalGameOfLifeState = temporalGameOfLifeState,
            interactiveCellUniverseState = interactiveCellUniverseState,
            cellWindowState = interactiveCellUniverseState.mutableCellWindowState,
            windowSizeClass = windowSizeClass,
        )
    }
}

interface InteractiveCellUniverseState {

    /**
     * `true` if the viewport is tracking the alive cells.
     */
    var isViewportTracking: Boolean

    /**
     * The [MutableCellWindowState] for use when [isViewportTracking] is `false`.
     */
    val mutableCellWindowState: MutableCellWindowState

    /**
     * The [TrackingCellWindowState] for use when [isViewportTracking] is `true`.
     */
    val trackingCellWindowState: TrackingCellWindowState

    /**
     * The [ViewportInteractionConfig].
     */
    val viewportInteractionConfig: ViewportInteractionConfig

    /**
     * `true` if the action card is the "top card", meaning that it should be preferred to be shown if there isn't
     * enough space to show both.
     */
    val isActionCardTopCard: Boolean

    /**
     * The info card state.
     */
    val infoCardState: CellUniverseInfoCardState

    /**
     * The action card state.
     */
    val actionCardState: CellUniverseActionCardState

    /**
     * `true` if the overlay is showing fullscreen. If this is the case, then the main cell window is entirely
     * obscured.
     */
    val isOverlayShowingFullscreen: Boolean
}

@Suppress("LongMethod", "CyclomaticComplexMethod")
@Composable
fun rememberInteractiveCellUniverseState(
    temporalGameOfLifeState: TemporalGameOfLifeState,
): InteractiveCellUniverseState {
    val mutableCellWindowState = rememberMutableCellWindowState()
    val trackingCellWindowState = rememberTrackingCellWindowState(temporalGameOfLifeState)

    var isViewportTracking by rememberSaveable { mutableStateOf(false) }

    var isActionCardTopCard by rememberSaveable { mutableStateOf(true) }

    val isInfoCardExpandedState = rememberSaveable { mutableStateOf(false) }
    val isActionCardExpandedState = rememberSaveable { mutableStateOf(false) }

    val isInfoCardExpanded = isInfoCardExpandedState.value
    fun setIsInfoCardExpanded(value: Boolean) {
        isInfoCardExpandedState.value = value
        if (value) {
            isActionCardExpandedState.value = false
            isActionCardTopCard = false
        }
    }

    val isActionCardExpanded = isActionCardExpandedState.value
    fun setIsActionCardExpanded(value: Boolean) {
        isActionCardExpandedState.value = value
        if (value) {
            isInfoCardExpandedState.value = false
            isActionCardTopCard = true
        }
    }

    val infoCardExpandedPredictiveBackState = if (isInfoCardExpanded && !isActionCardTopCard) {
        predictiveBackHandler {
            setIsInfoCardExpanded(false)
        }
    } else {
        PredictiveBackState.NotRunning
    }
    val actionCardExpandedPredictiveBackState = if (isActionCardExpanded) {
        predictiveBackHandler {
            setIsActionCardExpanded(false)
        }
    } else {
        PredictiveBackState.NotRunning
    }

    val infoCardState = rememberCellUniverseInfoCardState(
        setIsExpanded = ::setIsInfoCardExpanded,
        expandedTargetState = when (infoCardExpandedPredictiveBackState) {
            PredictiveBackState.NotRunning -> TargetState.Single(isInfoCardExpanded)
            is PredictiveBackState.Running -> {
                check(isInfoCardExpanded)
                TargetState.InProgress(
                    current = true,
                    provisional = false,
                    progress = infoCardExpandedPredictiveBackState.progress,
                )
            }
        },
    )
    val actionCardState = rememberCellUniverseActionCardState(
        setIsExpanded = ::setIsActionCardExpanded,
        enableBackHandler = isActionCardTopCard,
        expandedTargetState = when (actionCardExpandedPredictiveBackState) {
            PredictiveBackState.NotRunning -> TargetState.Single(isActionCardExpanded)
            is PredictiveBackState.Running -> {
                check(isActionCardExpanded)
                TargetState.InProgress(
                    current = true,
                    provisional = false,
                    progress = actionCardExpandedPredictiveBackState.progress,
                )
            }
        },
    )

    return remember(mutableCellWindowState, trackingCellWindowState, infoCardState, actionCardState) {
        object : InteractiveCellUniverseState {
            override var isViewportTracking: Boolean
                get() = isViewportTracking
                set(value) {
                    isViewportTracking = value
                }
            override val mutableCellWindowState: MutableCellWindowState = mutableCellWindowState
            override val trackingCellWindowState: TrackingCellWindowState = trackingCellWindowState

            override val viewportInteractionConfig: ViewportInteractionConfig by derivedStateOf {
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
            override val isActionCardTopCard: Boolean
                get() = isActionCardTopCard
            override val infoCardState: CellUniverseInfoCardState = infoCardState
            override val actionCardState: CellUniverseActionCardState = actionCardState

            override val isOverlayShowingFullscreen: Boolean by derivedStateOf {
                val isTargetingFullscreen = when (
                    val fullscreenTargetState = actionCardState.fullscreenTargetState
                ) {
                    is TargetState.InProgress -> false
                    is TargetState.Single -> fullscreenTargetState.current
                }
                isTargetingFullscreen
            }
        }
    }
}
