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

import android.content.ClipData
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
import androidx.compose.ui.input.key.isCtrlPressed
import androidx.compose.ui.input.key.key
import androidx.compose.ui.input.key.onKeyEvent
import androidx.compose.ui.input.key.type
import androidx.compose.ui.platform.testTag
import androidx.compose.ui.unit.IntRect
import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.model.CellWindow
import com.alexvanyo.composelife.model.RunLengthEncodedCellStateSerializer
import com.alexvanyo.composelife.model.TemporalGameOfLifeState
import com.alexvanyo.composelife.model.isRunning
import com.alexvanyo.composelife.ui.app.action.CellUniverseActionCardState
import com.alexvanyo.composelife.ui.app.action.rememberCellUniverseActionCardState
import com.alexvanyo.composelife.ui.app.cells.CellWindowInteractionState
import com.alexvanyo.composelife.ui.app.cells.CellWindowLocalEntryPoint
import com.alexvanyo.composelife.ui.app.cells.MutableCellWindow
import com.alexvanyo.composelife.ui.app.cells.MutableCellWindowInteractionState
import com.alexvanyo.composelife.ui.app.cells.MutableCellWindowViewportState
import com.alexvanyo.composelife.ui.app.cells.SelectionState
import com.alexvanyo.composelife.ui.app.cells.TrackingCellWindowViewportState
import com.alexvanyo.composelife.ui.app.cells.ViewportInteractionConfig
import com.alexvanyo.composelife.ui.app.cells.rememberMutableCellWindowViewportState
import com.alexvanyo.composelife.ui.app.cells.rememberTrackingCellWindowViewportState
import com.alexvanyo.composelife.ui.app.info.CellUniverseInfoCardState
import com.alexvanyo.composelife.ui.app.info.rememberCellUniverseInfoCardState
import com.alexvanyo.composelife.ui.util.PredictiveBackHandler
import com.alexvanyo.composelife.ui.util.PredictiveBackState
import com.alexvanyo.composelife.ui.util.TargetState
import com.alexvanyo.composelife.ui.util.rememberClipboardState
import com.alexvanyo.composelife.ui.util.rememberPredictiveBackStateHolder

interface InteractiveCellUniverseInjectEntryPoint :
    InteractiveCellUniverseOverlayInjectEntryPoint

interface InteractiveCellUniverseLocalEntryPoint :
    CellWindowLocalEntryPoint,
    InteractiveCellUniverseOverlayLocalEntryPoint

/**
 * An interactive cell universe displaying the given [temporalGameOfLifeState] and the controls for adjusting how it
 * evolves.
 */
context(InteractiveCellUniverseInjectEntryPoint, InteractiveCellUniverseLocalEntryPoint)
@Suppress("LongParameterList", "LongMethod")
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
                        when (keyEvent.type) {
                            KeyEventType.KeyUp -> {
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
                                        true
                                    } else {
                                        false
                                    }
                                    Key.X -> if (keyEvent.isCtrlPressed) {
                                        interactiveCellUniverseState.onCut()
                                        true
                                    } else {
                                        false
                                    }
                                    else -> false
                                }
                            }
                            else -> false
                        }
                    }
                },
            ),
    ) {
        if (!interactiveCellUniverseState.isOverlayShowingFullscreen) {
            MutableCellWindow(
                gameOfLifeState = temporalGameOfLifeState,
                modifier = Modifier.testTag("MutableCellWindow"),
                cellWindowInteractionState = interactiveCellUniverseState.cellWindowInteractionState,
            )
        }

        InteractiveCellUniverseOverlay(
            temporalGameOfLifeState = temporalGameOfLifeState,
            interactiveCellUniverseState = interactiveCellUniverseState,
            cellWindowViewportState = interactiveCellUniverseState.mutableCellWindowViewportState,
            windowSizeClass = windowSizeClass,
            onCopy = interactiveCellUniverseState::onCopy,
            onCut = interactiveCellUniverseState::onCut,
        )
    }
}

interface InteractiveCellUniverseState {

    /**
     * `true` if the viewport is tracking the alive cells.
     */
    var isViewportTracking: Boolean

    /**
     * The [MutableCellWindowViewportState] for use when [isViewportTracking] is `false`.
     */
    val mutableCellWindowViewportState: MutableCellWindowViewportState

    /**
     * The [TrackingCellWindowViewportState] for use when [isViewportTracking] is `true`.
     */
    val trackingCellWindowViewportState: TrackingCellWindowViewportState

    /**
     * The [CellWindowInteractionState] containing the [ViewportInteractionConfig] and [SelectionState].
     */
    val cellWindowInteractionState: MutableCellWindowInteractionState

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

    /**
     * Copies the current selection (if any) to the system clipboard.
     */
    fun onCopy()

    /**
     * Cuts the current selection (if any) to the system clipboard.
     */
    fun onCut()

    /**
     * Selects the entire cell state.
     */
    fun onSelectAll()
}

@Suppress("LongMethod", "CyclomaticComplexMethod")
@Composable
fun rememberInteractiveCellUniverseState(
    temporalGameOfLifeState: TemporalGameOfLifeState,
): InteractiveCellUniverseState {
    val mutableCellWindowViewportState = rememberMutableCellWindowViewportState()
    val trackingCellWindowViewportState = rememberTrackingCellWindowViewportState(temporalGameOfLifeState)

    var selectionState by rememberSaveable(stateSaver = SelectionState.Saver) {
        mutableStateOf(SelectionState.NoSelection)
    }

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

    val infoCardExpandedPredictiveBackStateHolder = rememberPredictiveBackStateHolder()
    PredictiveBackHandler(
        predictiveBackStateHolder = infoCardExpandedPredictiveBackStateHolder,
        enabled = isInfoCardExpanded && !isActionCardTopCard,
    ) {
        setIsInfoCardExpanded(false)
    }

    val actionCardExpandedPredictiveBackStateHolder = rememberPredictiveBackStateHolder()
    PredictiveBackHandler(
        predictiveBackStateHolder = actionCardExpandedPredictiveBackStateHolder,
        enabled = isActionCardExpanded,
    ) {
        setIsActionCardExpanded(false)
    }

    val infoCardState = rememberCellUniverseInfoCardState(
        setIsExpanded = ::setIsInfoCardExpanded,
        expandedTargetState = when (val predictiveBackState = infoCardExpandedPredictiveBackStateHolder.value) {
            PredictiveBackState.NotRunning -> TargetState.Single(isInfoCardExpanded)
            is PredictiveBackState.Running -> {
                check(isInfoCardExpanded)
                TargetState.InProgress(
                    current = true,
                    provisional = false,
                    progress = predictiveBackState.progress,
                )
            }
        },
    )
    val actionCardState = rememberCellUniverseActionCardState(
        setIsExpanded = ::setIsActionCardExpanded,
        enableBackHandler = isActionCardTopCard,
        expandedTargetState = when (val predictiveBackState = actionCardExpandedPredictiveBackStateHolder.value) {
            PredictiveBackState.NotRunning -> TargetState.Single(isActionCardExpanded)
            is PredictiveBackState.Running -> {
                check(isActionCardExpanded)
                TargetState.InProgress(
                    current = true,
                    provisional = false,
                    progress = predictiveBackState.progress,
                )
            }
        },
    )

    val viewportInteractionConfig: ViewportInteractionConfig by
        remember(mutableCellWindowViewportState, trackingCellWindowViewportState) {
            derivedStateOf {
                if (isViewportTracking) {
                    ViewportInteractionConfig.Tracking(
                        trackingCellWindowViewportState = trackingCellWindowViewportState,
                        syncableMutableCellWindowViewportStates = listOf(mutableCellWindowViewportState),
                    )
                } else {
                    ViewportInteractionConfig.Navigable(
                        mutableCellWindowViewportState = mutableCellWindowViewportState,
                    )
                }
            }
        }

    val clipboardState = rememberClipboardState()

    return remember(
        temporalGameOfLifeState,
        mutableCellWindowViewportState,
        trackingCellWindowViewportState,
        infoCardState,
        actionCardState,
        clipboardState,
    ) {
        object : InteractiveCellUniverseState {
            override var isViewportTracking: Boolean
                get() = isViewportTracking
                set(value) {
                    isViewportTracking = value
                }
            override val mutableCellWindowViewportState: MutableCellWindowViewportState =
                mutableCellWindowViewportState
            override val trackingCellWindowViewportState: TrackingCellWindowViewportState =
                trackingCellWindowViewportState

            override val cellWindowInteractionState: MutableCellWindowInteractionState by derivedStateOf {
                object : MutableCellWindowInteractionState {
                    override val viewportInteractionConfig: ViewportInteractionConfig = viewportInteractionConfig
                    override var selectionState: SelectionState
                        get() = selectionState
                        set(value) {
                            selectionState = value
                        }
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

            override fun onCopy() = onCopy(isCut = false)

            override fun onCut() = onCopy(isCut = true)

            private fun onCopy(isCut: Boolean) {
                when (val currentSelectionState = selectionState) {
                    SelectionState.NoSelection,
                    is SelectionState.Selection,
                    -> Unit
                    is SelectionState.SelectingBox -> {
                        if (currentSelectionState.width != 0 && currentSelectionState.height != 0) {
                            val left: Int
                            val right: Int

                            if (currentSelectionState.width < 0) {
                                left = currentSelectionState.topLeft.x + currentSelectionState.width + 1
                                right = currentSelectionState.topLeft.x + 1
                            } else {
                                left = currentSelectionState.topLeft.x
                                right = currentSelectionState.topLeft.x + currentSelectionState.width
                            }

                            val top: Int
                            val bottom: Int

                            if (currentSelectionState.height < 0) {
                                top = currentSelectionState.topLeft.y + currentSelectionState.height + 1
                                bottom = currentSelectionState.topLeft.y + 1
                            } else {
                                top = currentSelectionState.topLeft.y
                                bottom = currentSelectionState.topLeft.y + currentSelectionState.height
                            }

                            val cellWindow = CellWindow(
                                IntRect(
                                    left = left,
                                    top = top,
                                    right = right,
                                    bottom = bottom,
                                ),
                            )

                            val aliveCells = temporalGameOfLifeState.cellState.getAliveCellsInWindow(cellWindow).toSet()

                            if (isCut) {
                                temporalGameOfLifeState.cellState =
                                    aliveCells.fold(temporalGameOfLifeState.cellState) { cellState, offset ->
                                        cellState.withCell(offset, false)
                                    }
                            }

                            val serializedCellState = RunLengthEncodedCellStateSerializer.serializeToString(
                                CellState(aliveCells),
                            )

                            clipboardState.clipData = ClipData.newPlainText(
                                "Cell state",
                                serializedCellState.joinToString("\n"),
                            )
                        }
                    }
                }
            }

            override fun onSelectAll() {
                val boundingBox = temporalGameOfLifeState.cellState.boundingBox
                selectionState =
                    SelectionState.SelectingBox(
                        topLeft = boundingBox.topLeft,
                        width = boundingBox.width + 1,
                        height = boundingBox.height + 1,
                    )
            }
        }
    }
}
