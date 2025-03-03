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

package com.alexvanyo.composelife.ui.app.action

import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateListOf
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.runtime.setValue
import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.model.CellStateParser
import com.alexvanyo.composelife.model.DeserializationResult
import com.alexvanyo.composelife.model.di.CellStateParserProvider
import com.alexvanyo.composelife.preferences.ToolConfig
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.di.LoadedComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.setMouseToolConfig
import com.alexvanyo.composelife.preferences.setStylusToolConfig
import com.alexvanyo.composelife.preferences.setTouchToolConfig
import com.alexvanyo.composelife.ui.app.parseCellState
import com.alexvanyo.composelife.ui.cells.isSharedElementForCellsSupported
import com.alexvanyo.composelife.ui.util.ClipboardReader
import com.alexvanyo.composelife.ui.util.clipboardStateKey
import com.alexvanyo.composelife.ui.util.rememberClipboardReader
import com.slack.circuit.retained.rememberRetained
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.launch
import kotlin.uuid.Uuid
import kotlin.collections.removeLast as removeLastKt

interface InlineEditPaneInjectEntryPoint :
    ComposeLifePreferencesProvider,
    CellStateParserProvider,
    ClipboardCellStatePreviewInjectEntryPoint

interface InlineEditPaneLocalEntryPoint :
    LoadedComposeLifePreferencesProvider,
    ClipboardCellStatePreviewLocalEntryPoint

interface InlineEditPaneState {
    val touchToolConfig: ToolConfig
    fun setTouchToolConfig(toolConfig: ToolConfig)
    val stylusToolConfig: ToolConfig
    fun setStylusToolConfig(toolConfig: ToolConfig)
    val mouseToolConfig: ToolConfig
    fun setMouseToolConfig(toolConfig: ToolConfig)

    val clipboardWatchingState: ClipboardWatchingState
}

sealed interface ClipboardWatchingState {

    interface Onboarding : ClipboardWatchingState {

        fun onAllowClipboardWatching()

        fun onDisallowClipboardWatching()
    }

    data object ClipboardWatchingDisabled : ClipboardWatchingState

    interface ClipboardWatchingEnabled : ClipboardWatchingState {
        val useSharedElementForCellStatePreviews: Boolean

        val isLoading: Boolean

        val clipboardPreviewStates: List<ClipboardPreviewState>

        val pinnedClipboardPreviewStates: List<PinnedClipboardPreviewState>
    }
}

interface ClipboardPreviewState {
    val id: Uuid
    val deserializationResult: DeserializationResult

    val isPinned: Boolean

    fun onPaste()

    fun onPinChanged()

    fun onViewDeserializationInfo()
}

interface PinnedClipboardPreviewState {
    val id: Uuid
    val deserializationResult: DeserializationResult.Successful

    fun onPaste()

    fun onUnpin()

    fun onViewDeserializationInfo()
}

context(
    ComposeLifePreferencesProvider,
    LoadedComposeLifePreferencesProvider,
    CellStateParserProvider
)
@Composable
fun rememberInlineEditPaneState(
    setSelectionToCellState: (CellState) -> Unit,
    onViewDeserializationInfo: (DeserializationResult) -> Unit,
): InlineEditPaneState {
    val coroutineScope = rememberCoroutineScope()

    val clipboardWatchingState = rememberClipboardWatchingState(
        coroutineScope = coroutineScope,
        setSelectionToCellState = setSelectionToCellState,
        onViewDeserializationInfo = onViewDeserializationInfo,
    )

    return remember(coroutineScope, composeLifePreferences, preferences, clipboardWatchingState) {
        object : InlineEditPaneState {
            override val touchToolConfig: ToolConfig
                get() = preferences.touchToolConfig

            override fun setTouchToolConfig(toolConfig: ToolConfig) {
                coroutineScope.launch {
                    composeLifePreferences.setTouchToolConfig(toolConfig)
                }
            }

            override val stylusToolConfig: ToolConfig get() =
                preferences.stylusToolConfig

            override fun setStylusToolConfig(toolConfig: ToolConfig) {
                coroutineScope.launch {
                    composeLifePreferences.setStylusToolConfig(toolConfig)
                }
            }

            override val mouseToolConfig: ToolConfig get() =
                preferences.mouseToolConfig

            override fun setMouseToolConfig(toolConfig: ToolConfig) {
                coroutineScope.launch {
                    composeLifePreferences.setMouseToolConfig(toolConfig)
                }
            }

            override val clipboardWatchingState get() = clipboardWatchingState
        }
    }
}

context(
    ComposeLifePreferencesProvider,
    LoadedComposeLifePreferencesProvider,
    CellStateParserProvider
)
@Composable
fun rememberClipboardWatchingState(
    setSelectionToCellState: (CellState) -> Unit,
    onViewDeserializationInfo: (DeserializationResult) -> Unit,
    coroutineScope: CoroutineScope = rememberCoroutineScope(),
): ClipboardWatchingState =
    if (preferences.completedClipboardWatchingOnboarding) {
        if (preferences.enableClipboardWatching) {
            rememberClipboardWatchingEnabledState(setSelectionToCellState, onViewDeserializationInfo)
        } else {
            ClipboardWatchingState.ClipboardWatchingDisabled
        }
    } else {
        rememberClipboardWatchingOnboardingState(coroutineScope)
    }

context(ComposeLifePreferencesProvider)
@Composable
fun rememberClipboardWatchingOnboardingState(
    coroutineScope: CoroutineScope = rememberCoroutineScope(),
): ClipboardWatchingState.Onboarding =
    remember(coroutineScope, composeLifePreferences) {
        object : ClipboardWatchingState.Onboarding {
            override fun onAllowClipboardWatching() {
                coroutineScope.launch {
                    composeLifePreferences.update {
                        setEnableClipboardWatching(true)
                        setCompletedClipboardWatchingOnboarding(true)
                    }
                }
            }

            override fun onDisallowClipboardWatching() {
                coroutineScope.launch {
                    composeLifePreferences.update {
                        setEnableClipboardWatching(false)
                        setCompletedClipboardWatchingOnboarding(true)
                    }
                }
            }
        }
    }

context(CellStateParserProvider, LoadedComposeLifePreferencesProvider)
@Composable
fun rememberClipboardWatchingEnabledState(
    setSelectionToCellState: (CellState) -> Unit,
    onViewDeserializationInfo: (DeserializationResult) -> Unit,
): ClipboardWatchingState.ClipboardWatchingEnabled =
    rememberClipboardWatchingEnabledState(
        useSharedElementForCellStatePreviews = isSharedElementForCellsSupported(isThumbnail = true),
        clipboardReader = rememberClipboardReader(),
        parser = cellStateParser,
        setSelectionToCellState = setSelectionToCellState,
        onViewDeserializationInfo = onViewDeserializationInfo,
    )

context(LoadedComposeLifePreferencesProvider)
@Suppress("LongMethod")
@Composable
fun rememberClipboardWatchingEnabledState(
    useSharedElementForCellStatePreviews: Boolean,
    clipboardReader: ClipboardReader,
    parser: CellStateParser,
    setSelectionToCellState: (CellState) -> Unit,
    onViewDeserializationInfo: (DeserializationResult) -> Unit,
): ClipboardWatchingState.ClipboardWatchingEnabled {
    var isLoading by remember { mutableStateOf(false) }
    var currentClipboardCellStateId: Uuid by rememberRetained {
        mutableStateOf(Uuid.random())
    }
    var currentDeserializationResult: DeserializationResult? by rememberRetained {
        mutableStateOf(null)
    }
    val previousClipboardCellStates: MutableList<Pair<Uuid, DeserializationResult.Successful>> = rememberRetained {
        mutableStateListOf()
    }
    val pinnedClipboardCellStates: MutableList<Pair<Uuid, DeserializationResult.Successful>> = rememberRetained {
        mutableStateListOf()
    }

    LaunchedEffect(clipboardReader, clipboardReader.clipboardStateKey, parser) {
        // There is potentially a new cell state from the clipboard, mark for the UI that we are loading it
        isLoading = true

        // Parse the cell state
        val newClipboardCellStateResourceState = parser.parseCellState(clipboardReader)

        // Parsing has completed, we are no longer loading
        isLoading = false

        // If the newly parsed deserialization result is the same as the current one, then we don't
        // have anything to do. In other words, after re-parsing we got the same cell state.
        if (currentDeserializationResult != newClipboardCellStateResourceState) {
            // Otherwise, we have a differing deserialization result
            val previousDeserializationResult = currentDeserializationResult
            if (
                previousDeserializationResult != null &&
                previousDeserializationResult is DeserializationResult.Successful
            ) {
                // If the previous deserialization result was successful, then we should save it to the
                // clipboard history at the beginning of the list, keeping the old clipboard cell state id
                previousClipboardCellStates.add(
                    0,
                    currentClipboardCellStateId to previousDeserializationResult,
                )
                // Trim the clipboard history down
                while (previousClipboardCellStates.size > 4) {
                    previousClipboardCellStates.removeLastKt()
                }

                // We have "locked" in a successful clipboard parsing result into history, so start creating
                // a new one
                currentClipboardCellStateId = Uuid.random()
            }

            // Bring the deserialization result up-to-date
            currentDeserializationResult = newClipboardCellStateResourceState
        }
    }

    return remember(setSelectionToCellState, useSharedElementForCellStatePreviews) {
        object : ClipboardWatchingState.ClipboardWatchingEnabled {
            override val isLoading: Boolean
                get() = isLoading

            override val useSharedElementForCellStatePreviews: Boolean = useSharedElementForCellStatePreviews

            override val clipboardPreviewStates: List<ClipboardPreviewState>
                get() = listOfNotNull(
                    currentDeserializationResult?.let { deserializationResult ->
                        object : ClipboardPreviewState {
                            override val id = currentClipboardCellStateId
                            override val deserializationResult = deserializationResult

                            override val isPinned get() = pinnedClipboardCellStates.any { it.first == id }

                            override fun onPaste() {
                                when (deserializationResult) {
                                    is DeserializationResult.Successful -> {
                                        setSelectionToCellState(deserializationResult.cellState)
                                    }
                                    is DeserializationResult.Unsuccessful -> Unit
                                }
                            }

                            override fun onPinChanged() {
                                when (deserializationResult) {
                                    is DeserializationResult.Successful -> {
                                        if (isPinned) {
                                            pinnedClipboardCellStates.removeIf { it.first == id }
                                        } else {
                                            pinnedClipboardCellStates.add(id to deserializationResult)
                                        }
                                    }
                                    is DeserializationResult.Unsuccessful -> Unit
                                }
                            }

                            override fun onViewDeserializationInfo() {
                                onViewDeserializationInfo(deserializationResult)
                            }
                        }
                    },
                ) + previousClipboardCellStates.map { (id, deserializationResult) ->
                    object : ClipboardPreviewState {
                        override val id = id
                        override val deserializationResult = deserializationResult

                        override val isPinned get() = pinnedClipboardCellStates.any { it.first == id }

                        override fun onPaste() {
                            setSelectionToCellState(deserializationResult.cellState)
                        }

                        override fun onPinChanged() {
                            if (isPinned) {
                                pinnedClipboardCellStates.removeIf { it.first == id }
                            } else {
                                pinnedClipboardCellStates.add(id to deserializationResult)
                            }
                        }

                        override fun onViewDeserializationInfo() {
                            onViewDeserializationInfo(deserializationResult)
                        }
                    }
                }

            override val pinnedClipboardPreviewStates: List<PinnedClipboardPreviewState>
                get() = pinnedClipboardCellStates.map { (id, deserializationResult) ->
                    object : PinnedClipboardPreviewState {
                        override val id = id
                        override val deserializationResult = deserializationResult

                        override fun onPaste() {
                            setSelectionToCellState(deserializationResult.cellState)
                        }

                        override fun onUnpin() {
                            pinnedClipboardCellStates.removeIf { it.first == id }
                        }

                        override fun onViewDeserializationInfo() {
                            onViewDeserializationInfo(deserializationResult)
                        }
                    }
                }
        }
    }
}
