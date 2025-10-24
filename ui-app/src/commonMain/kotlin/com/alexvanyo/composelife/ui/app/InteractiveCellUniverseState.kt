/*
 * Copyright 2025 The Android Open Source Project
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

import androidx.compose.runtime.Composable
import androidx.compose.runtime.Immutable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.collectAsState
import androidx.compose.runtime.derivedStateOf
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.unit.round
import androidx.navigationevent.NavigationEventInfo
import androidx.navigationevent.NavigationEventTransitionState
import androidx.navigationevent.compose.LocalNavigationEventDispatcherOwner
import androidx.navigationevent.compose.NavigationBackHandler
import androidx.navigationevent.compose.rememberNavigationEventState
import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.model.CellStateParser
import com.alexvanyo.composelife.model.DeserializationResult
import com.alexvanyo.composelife.model.RunLengthEncodedCellStateSerializer
import com.alexvanyo.composelife.model.TemporalGameOfLifeState
import com.alexvanyo.composelife.sessionvalue.SessionValue
import com.alexvanyo.composelife.ui.app.action.CellUniverseActionCardState
import com.alexvanyo.composelife.ui.app.action.rememberCellUniverseActionCardState
import com.alexvanyo.composelife.ui.app.info.CellUniverseInfoCardState
import com.alexvanyo.composelife.ui.app.info.rememberCellUniverseInfoCardState
import com.alexvanyo.composelife.ui.cells.CellWindowInteractionState
import com.alexvanyo.composelife.ui.cells.MutableCellWindowCtx
import com.alexvanyo.composelife.ui.cells.MutableCellWindowInteractionState
import com.alexvanyo.composelife.ui.cells.MutableCellWindowViewportState
import com.alexvanyo.composelife.ui.cells.MutableSelectionStateHolder
import com.alexvanyo.composelife.ui.cells.SelectionState
import com.alexvanyo.composelife.ui.cells.TrackingCellWindowViewportState
import com.alexvanyo.composelife.ui.cells.ViewportInteractionConfig
import com.alexvanyo.composelife.ui.cells.getSelectedCellState
import com.alexvanyo.composelife.ui.cells.rememberMutableCellWindowViewportState
import com.alexvanyo.composelife.ui.cells.rememberMutableSelectionStateHolder
import com.alexvanyo.composelife.ui.cells.rememberTrackingCellWindowViewportState
import com.alexvanyo.composelife.ui.mobile.rememberSpatialController
import com.alexvanyo.composelife.ui.util.ClipboardReaderWriter
import com.alexvanyo.composelife.ui.util.ImmersiveModeManager
import com.alexvanyo.composelife.ui.util.LocalGhostElement
import com.alexvanyo.composelife.ui.util.TargetState
import com.alexvanyo.composelife.ui.util.rememberClipboardReaderWriter
import com.alexvanyo.composelife.ui.util.setText
import dev.zacsweers.metro.Inject
import kotlinx.coroutines.launch
import kotlin.uuid.Uuid

// region templated-ctx
@Immutable
@Inject
class InteractiveCellUniverseCtx(
    internal val cellStateParser: CellStateParser,
    internal val immersiveModeManager: ImmersiveModeManager,
    internal val mutableCellWindowCtx: MutableCellWindowCtx,
    internal val interactiveCellUniverseOverlayCtx: InteractiveCellUniverseOverlayCtx,
) {
    companion object
}
// endregion templated-ctx

interface InteractiveCellUniverseState {

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

    val editingState: InteractiveCellUniverseEditingState
}

interface InteractiveCellUniverseEditingState {
    val selectionState: SelectionState

    /**
     * Copies the current selection (if any) to the system clipboard.
     *
     * Returns `true` if the copy is triggered.
     */
    fun onCopy(): Boolean

    /**
     * Cuts the current selection (if any) to the system clipboard.
     *
     * Returns `true` if the cut is triggered.
     */
    fun onCut(): Boolean

    /**
     * Pastes the current selection (if any) from the system clipboard.
     */
    fun onPaste()

    /**
     * Applies the current paste, updating the cell state.
     *
     * Returns `true` if the paste is applied.
     */
    fun onApplyPaste(): Boolean

    /**
     * Selects the entire cell state.
     */
    fun onSelectAll()

    /**
     * Sets the selection to the given [cellState].
     *
     * The resulting selection will be centered on the current viewport.
     */
    fun setSelectionToCellState(cellState: CellState)

    /**
     * Clears the selection (if any)
     */
    fun onClearSelection()
}

context(ctx: InteractiveCellUniverseCtx)
@Suppress("LongMethod", "CyclomaticComplexMethod")
@Composable
fun rememberInteractiveCellUniverseState(
    temporalGameOfLifeState: TemporalGameOfLifeState,
    mutableCellWindowViewportState: MutableCellWindowViewportState = rememberMutableCellWindowViewportState(),
    clipboardReaderWriter: ClipboardReaderWriter = rememberClipboardReaderWriter(),
): InteractiveCellUniverseState =
    rememberInteractiveCellUniverseState(
        cellStateParser = ctx.cellStateParser,
        immersiveModeManager = ctx.immersiveModeManager,
        temporalGameOfLifeState = temporalGameOfLifeState,
        mutableCellWindowViewportState = mutableCellWindowViewportState,
        clipboardReaderWriter = clipboardReaderWriter,
    )

@Suppress("LongMethod", "CyclomaticComplexMethod")
@Composable
internal fun rememberInteractiveCellUniverseState(
    cellStateParser: CellStateParser,
    immersiveModeManager: ImmersiveModeManager,
    temporalGameOfLifeState: TemporalGameOfLifeState,
    mutableCellWindowViewportState: MutableCellWindowViewportState = rememberMutableCellWindowViewportState(),
    clipboardReaderWriter: ClipboardReaderWriter = rememberClipboardReaderWriter(),
): InteractiveCellUniverseState {
    val trackingCellWindowViewportState = rememberTrackingCellWindowViewportState(temporalGameOfLifeState)

    val selectionStateHolder = rememberMutableSelectionStateHolder(
        SessionValue(Uuid.random(), Uuid.random(), SelectionState.NoSelection),
    )

    val coroutineScope = rememberCoroutineScope()

    var isViewportTracking by rememberSaveable { mutableStateOf(false) }

    var isImmersiveMode by rememberSaveable { mutableStateOf(false) }

    if (!LocalGhostElement.current) {
        if (isImmersiveMode) {
            LaunchedEffect(Unit) {
                immersiveModeManager.enterFullscreenMode()
                immersiveModeManager.hideSystemUi()
            }
        } else {
            LaunchedEffect(Unit) {
                immersiveModeManager.exitFullscreenMode()
            }
        }
    }

    val spatialController = rememberSpatialController()

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

    val dispatcher = requireNotNull(LocalNavigationEventDispatcherOwner.current).navigationEventDispatcher

    val navigationEventHistory by dispatcher.history.collectAsState()
    val currentInfo = navigationEventHistory.mergedHistory.getOrNull(navigationEventHistory.currentIndex)

    val infoCardNavigationEventTransitionState =
        if (currentInfo is InfoCardNavigationEventInfo) {
            dispatcher.transitionState.collectAsState().value
        } else {
            NavigationEventTransitionState.Idle
        }
    NavigationBackHandler(
        state = rememberNavigationEventState(
            currentInfo = InfoCardNavigationEventInfo,
        ),
        isBackEnabled = isInfoCardExpanded && !isActionCardTopCard,
        onBackCompleted = { setIsInfoCardExpanded(false) },
    )

    val actionCardNavigationEventTransitionState =
        if (currentInfo is ActionCardNavigationEventInfo) {
            dispatcher.transitionState.collectAsState().value
        } else {
            NavigationEventTransitionState.Idle
        }
    NavigationBackHandler(
        state = rememberNavigationEventState(
            currentInfo = ActionCardNavigationEventInfo,
        ),
        isBackEnabled = isActionCardExpanded,
        onBackCompleted = { setIsActionCardExpanded(false) },
    )

    val editingState = remember(
        selectionStateHolder,
        temporalGameOfLifeState,
        coroutineScope,
        clipboardReaderWriter,
        cellStateParser,
    ) {
        object : InteractiveCellUniverseEditingState {
            override val selectionState: SelectionState
                get() = selectionStateHolder.selectionSessionState.value

            override fun onCopy() = onCopy(isCut = false)

            override fun onCut() = onCopy(isCut = true)

            private fun onCopy(isCut: Boolean): Boolean =
                when (val currentSelectionState = selectionStateHolder.selectionSessionState.value) {
                    SelectionState.NoSelection,
                    is SelectionState.Selection,
                    is SelectionState.SelectingBox.TransientSelectingBox,
                    -> false
                    is SelectionState.SelectingBox.FixedSelectingBox -> {
                        if (currentSelectionState.width != 0 && currentSelectionState.height != 0) {
                            val selectedCellState =
                                temporalGameOfLifeState.cellState.getSelectedCellState(currentSelectionState)

                            if (isCut) {
                                temporalGameOfLifeState.cellState =
                                    temporalGameOfLifeState.cellState.subtract(selectedCellState)
                            }

                            coroutineScope.launch {
                                val serializedCellState = RunLengthEncodedCellStateSerializer.serializeToString(
                                    selectedCellState,
                                )

                                clipboardReaderWriter.setText(serializedCellState.joinToString("\n"))
                            }
                            true
                        } else {
                            false
                        }
                    }
                }

            override fun onPaste() {
                coroutineScope.launch {
                    when (
                        val deserializationResult =
                            cellStateParser.parseCellState(clipboardReaderWriter)
                    ) {
                        is DeserializationResult.Successful -> {
                            setSelectionToCellState(deserializationResult.cellState)
                        }
                        is DeserializationResult.Unsuccessful -> {
                            // TODO: Show error for unsuccessful pasting
                        }
                    }
                }
            }

            override fun onApplyPaste(): Boolean =
                when (val currentSelectionState = selectionStateHolder.selectionSessionState.value) {
                    SelectionState.NoSelection,
                    is SelectionState.SelectingBox,
                    -> false
                    is SelectionState.Selection -> {
                        val selectionCellState = currentSelectionState.cellState

                        temporalGameOfLifeState.cellState = selectionCellState.aliveCells
                            .fold(temporalGameOfLifeState.cellState) { cellState, offset ->
                                cellState.withCell(
                                    offset = offset +
                                        currentSelectionState.offset -
                                        selectionCellState.boundingBox.topLeft,
                                    isAlive = true,
                                )
                            }
                        selectionStateHolder.selectionSessionState =
                            SessionValue(Uuid.random(), Uuid.random(), SelectionState.NoSelection)
                        true
                    }
                }

            override fun onSelectAll() {
                val boundingBox = temporalGameOfLifeState.cellState.boundingBox
                selectionStateHolder.selectionSessionState = SessionValue(
                    sessionId = Uuid.random(),
                    valueId = Uuid.random(),
                    value = SelectionState.SelectingBox.FixedSelectingBox(
                        topLeft = boundingBox.topLeft,
                        width = boundingBox.width + 1,
                        height = boundingBox.height + 1,
                        previousTransientSelectingBox = null,
                    ),
                )
            }

            override fun onClearSelection() {
                selectionStateHolder.selectionSessionState =
                    SessionValue(Uuid.random(), Uuid.random(), SelectionState.NoSelection)
            }

            override fun setSelectionToCellState(cellState: CellState) {
                val boundingBoxSize = cellState.boundingBox.size
                selectionStateHolder.selectionSessionState = SessionValue(
                    sessionId = Uuid.random(),
                    valueId = Uuid.random(),
                    value = SelectionState.Selection(
                        cellState = cellState,
                        offset = (
                            mutableCellWindowViewportState.cellWindowViewport.offset -
                                Offset(boundingBoxSize.width - 1f, boundingBoxSize.height - 1f) / 2f
                            ).round(),
                    ),
                )
            }
        }
    }

    val infoCardState = rememberCellUniverseInfoCardState(
        setIsExpanded = ::setIsInfoCardExpanded,
        expandedTargetState = when (val navEventState = infoCardNavigationEventTransitionState) {
            is NavigationEventTransitionState.Idle -> TargetState.Single(isInfoCardExpanded)
            is NavigationEventTransitionState.InProgress -> {
                check(isInfoCardExpanded)
                TargetState.InProgress(
                    current = true,
                    provisional = false,
                    progress = navEventState.latestEvent.progress,
                )
            }
        },
    )
    val actionCardState = rememberCellUniverseActionCardState(
        enableBackHandler = isActionCardTopCard,
        isViewportTracking = isViewportTracking,
        setIsViewportTracking = { isViewportTracking = it },
        showImmersiveModeControl = !spatialController.hasXrSpatialFeature,
        isImmersiveMode = isImmersiveMode,
        setIsImmersiveMode = { isImmersiveMode = it },
        showFullSpaceModeControl = spatialController.hasXrSpatialFeature,
        isFullSpaceMode = spatialController.isFullSpaceMode,
        setIsFullSpaceMode = { spatialController.isFullSpaceMode = it },
        isExpanded = isActionCardExpanded,
        setIsExpanded = ::setIsActionCardExpanded,
        expandedTargetState = when (val navEventState = actionCardNavigationEventTransitionState) {
            is NavigationEventTransitionState.Idle -> TargetState.Single(isActionCardExpanded)
            is NavigationEventTransitionState.InProgress -> {
                check(isActionCardExpanded)
                TargetState.InProgress(
                    current = true,
                    provisional = false,
                    progress = navEventState.latestEvent.progress,
                )
            }
        },
        temporalGameOfLifeState = temporalGameOfLifeState,
        editingState = editingState,
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

    return remember(
        mutableCellWindowViewportState,
        trackingCellWindowViewportState,
        infoCardState,
        actionCardState,
        spatialController,
        editingState,
    ) {
        object : InteractiveCellUniverseState {
            override val mutableCellWindowViewportState: MutableCellWindowViewportState =
                mutableCellWindowViewportState
            override val trackingCellWindowViewportState: TrackingCellWindowViewportState =
                trackingCellWindowViewportState

            override val cellWindowInteractionState: MutableCellWindowInteractionState by derivedStateOf {
                object :
                    MutableCellWindowInteractionState,
                    MutableSelectionStateHolder by selectionStateHolder {
                    override val viewportInteractionConfig: ViewportInteractionConfig = viewportInteractionConfig
                }
            }

            override val isActionCardTopCard: Boolean
                get() = isActionCardTopCard
            override val infoCardState: CellUniverseInfoCardState = infoCardState
            override val actionCardState: CellUniverseActionCardState = actionCardState
            override val editingState: InteractiveCellUniverseEditingState = editingState
        }
    }
}

private object InfoCardNavigationEventInfo : NavigationEventInfo()

private object ActionCardNavigationEventInfo : NavigationEventInfo()
