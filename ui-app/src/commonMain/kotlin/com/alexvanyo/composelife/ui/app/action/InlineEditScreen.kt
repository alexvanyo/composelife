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

package com.alexvanyo.composelife.ui.app.action

import androidx.compose.foundation.ScrollState
import androidx.compose.foundation.layout.Arrangement
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.Row
import androidx.compose.foundation.layout.padding
import androidx.compose.foundation.rememberScrollState
import androidx.compose.foundation.verticalScroll
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.automirrored.filled.Backspace
import androidx.compose.material.icons.filled.Brush
import androidx.compose.material.icons.filled.Cancel
import androidx.compose.material.icons.filled.Draw
import androidx.compose.material.icons.filled.Mouse
import androidx.compose.material.icons.filled.PanTool
import androidx.compose.material.icons.filled.SelectAll
import androidx.compose.material.icons.filled.TouchApp
import androidx.compose.material3.Icon
import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateListOf
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.runtime.setValue
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.dispatchers.di.ComposeLifeDispatchersProvider
import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.model.DeserializationResult
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResource
import com.alexvanyo.composelife.preferences.ToolConfig
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.di.LoadedComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.setMouseToolConfig
import com.alexvanyo.composelife.preferences.setStylusToolConfig
import com.alexvanyo.composelife.preferences.setTouchToolConfig
import com.alexvanyo.composelife.ui.app.ClipboardCellStateParser
import com.alexvanyo.composelife.ui.app.ClipboardCellStateParserProvider
import com.alexvanyo.composelife.ui.app.component.DropdownOption
import com.alexvanyo.composelife.ui.app.component.TextFieldDropdown
import com.alexvanyo.composelife.ui.app.resources.Draw
import com.alexvanyo.composelife.ui.app.resources.Erase
import com.alexvanyo.composelife.ui.app.resources.Mouse
import com.alexvanyo.composelife.ui.app.resources.MouseTool
import com.alexvanyo.composelife.ui.app.resources.None
import com.alexvanyo.composelife.ui.app.resources.Pan
import com.alexvanyo.composelife.ui.app.resources.Select
import com.alexvanyo.composelife.ui.app.resources.Strings
import com.alexvanyo.composelife.ui.app.resources.Stylus
import com.alexvanyo.composelife.ui.app.resources.StylusTool
import com.alexvanyo.composelife.ui.app.resources.Touch
import com.alexvanyo.composelife.ui.app.resources.TouchTool
import com.alexvanyo.composelife.ui.util.ClipboardReader
import com.alexvanyo.composelife.ui.util.clipboardStateKey
import com.alexvanyo.composelife.ui.util.rememberClipboardReader
import com.livefront.sealedenum.GenSealedEnum
import com.slack.circuit.retained.rememberRetained
import kotlinx.collections.immutable.toImmutableList
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.launch
import java.util.UUID

interface InlineEditPaneInjectEntryPoint :
    ComposeLifePreferencesProvider,
    ComposeLifeDispatchersProvider,
    ClipboardCellStateParserProvider,
    ClipboardCellStatePreviewInjectEntryPoint

interface InlineEditPaneLocalEntryPoint :
    LoadedComposeLifePreferencesProvider,
    ClipboardCellStatePreviewLocalEntryPoint

context(InlineEditPaneInjectEntryPoint, InlineEditPaneLocalEntryPoint)
@Composable
fun InlineEditPane(
    setSelectionToCellState: (CellState) -> Unit,
    modifier: Modifier = Modifier,
    scrollState: ScrollState = rememberScrollState(),
) = InlineEditPane(
    state = rememberInlineEditPaneState(setSelectionToCellState),
    modifier = modifier,
    scrollState = scrollState,
)

context(ClipboardCellStatePreviewInjectEntryPoint, ClipboardCellStatePreviewLocalEntryPoint)
@Suppress("LongParameterList", "LongMethod")
@Composable
fun InlineEditPane(
    state: InlineEditPaneState,
    modifier: Modifier = Modifier,
    scrollState: ScrollState = rememberScrollState(),
) {
    Column(
        modifier
            .verticalScroll(scrollState)
            .padding(vertical = 8.dp),
    ) {
        ClipboardWatchingSection(
            clipboardWatchingState = state.clipboardWatchingState,
        )

        Row(
            verticalAlignment = Alignment.CenterVertically,
            horizontalArrangement = Arrangement.spacedBy(16.dp),
            modifier = Modifier.padding(horizontal = 16.dp),
        ) {
            Icon(
                imageVector = Icons.Filled.TouchApp,
                contentDescription = parameterizedStringResource(Strings.Touch),
                modifier = Modifier.padding(top = 8.dp),
            )
            TextFieldDropdown(
                label = parameterizedStringResource(Strings.TouchTool),
                currentValue = state.touchToolDropdownOption,
                allValues = ToolDropdownOption.values.toImmutableList(),
                setValue = state::setTouchToolDropdownOption,
            )
        }
        Row(
            verticalAlignment = Alignment.CenterVertically,
            horizontalArrangement = Arrangement.spacedBy(16.dp),
            modifier = Modifier.padding(horizontal = 16.dp),
        ) {
            Icon(
                imageVector = Icons.Filled.Brush,
                contentDescription = parameterizedStringResource(Strings.Stylus),
                modifier = Modifier.padding(top = 8.dp),
            )
            TextFieldDropdown(
                label = parameterizedStringResource(Strings.StylusTool),
                currentValue = state.stylusToolDropdownOption,
                allValues = ToolDropdownOption.values.toImmutableList(),
                setValue = state::setStylusToolDropdownOption,
            )
        }
        Row(
            verticalAlignment = Alignment.CenterVertically,
            horizontalArrangement = Arrangement.spacedBy(16.dp),
            modifier = Modifier.padding(horizontal = 16.dp),
        ) {
            Icon(
                imageVector = Icons.Filled.Mouse,
                contentDescription = parameterizedStringResource(Strings.Mouse),
                modifier = Modifier.padding(top = 8.dp),
            )
            TextFieldDropdown(
                label = parameterizedStringResource(Strings.MouseTool),
                currentValue = state.mouseToolDropdownOption,
                allValues = ToolDropdownOption.values.toImmutableList(),
                setValue = state::setMouseToolDropdownOption,
            )
        }
    }
}

sealed interface ToolDropdownOption : DropdownOption {
    data object Pan : ToolDropdownOption {
        override val displayText = Strings.Pan
        override val leadingIcon: (@Composable () -> Unit) = {
            Icon(
                imageVector = Icons.Default.PanTool,
                contentDescription = null,
            )
        }
    }
    data object Draw : ToolDropdownOption {
        override val displayText = Strings.Draw
        override val leadingIcon: (@Composable () -> Unit) = {
            Icon(
                imageVector = Icons.Default.Draw,
                contentDescription = null,
            )
        }
    }
    data object Erase : ToolDropdownOption {
        override val displayText = Strings.Erase
        override val leadingIcon: (@Composable () -> Unit) = {
            Icon(
                imageVector = Icons.AutoMirrored.Filled.Backspace,
                contentDescription = null,
            )
        }
    }
    data object Select : ToolDropdownOption {
        override val displayText = Strings.Select
        override val leadingIcon: (@Composable () -> Unit) = {
            Icon(
                imageVector = Icons.Default.SelectAll,
                contentDescription = null,
            )
        }
    }
    data object None : ToolDropdownOption {
        override val displayText = Strings.None
        override val leadingIcon: (@Composable () -> Unit) = {
            Icon(
                imageVector = Icons.Default.Cancel,
                contentDescription = null,
            )
        }
    }

    @GenSealedEnum
    companion object
}

private fun ToolDropdownOption.toToolConfig(): ToolConfig =
    when (this) {
        ToolDropdownOption.Draw -> ToolConfig.Draw
        ToolDropdownOption.Erase -> ToolConfig.Erase
        ToolDropdownOption.None -> ToolConfig.None
        ToolDropdownOption.Pan -> ToolConfig.Pan
        ToolDropdownOption.Select -> ToolConfig.Select
    }

private fun ToolConfig.toToolDropdownOption(): ToolDropdownOption =
    when (this) {
        ToolConfig.Draw -> ToolDropdownOption.Draw
        ToolConfig.Erase -> ToolDropdownOption.Erase
        ToolConfig.None -> ToolDropdownOption.None
        ToolConfig.Pan -> ToolDropdownOption.Pan
        ToolConfig.Select -> ToolDropdownOption.Select
    }

interface InlineEditPaneState {
    val touchToolDropdownOption: ToolDropdownOption
    fun setTouchToolDropdownOption(toolDropdownOption: ToolDropdownOption)
    val stylusToolDropdownOption: ToolDropdownOption
    fun setStylusToolDropdownOption(toolDropdownOption: ToolDropdownOption)
    val mouseToolDropdownOption: ToolDropdownOption
    fun setMouseToolDropdownOption(toolDropdownOption: ToolDropdownOption)

    val clipboardWatchingState: ClipboardWatchingState
}

sealed interface ClipboardWatchingState {

    interface Onboarding : ClipboardWatchingState {

        fun onAllowClipboardWatching()

        fun onDisallowClipboardWatching()
    }

    data object ClipboardWatchingDisabled : ClipboardWatchingState

    interface ClipboardWatchingEnabled : ClipboardWatchingState {
        val isLoading: Boolean

        val clipboardPreviewStates: List<ClipboardPreviewState>
    }
}

interface ClipboardPreviewState {
    val id: UUID
    val deserializationResult: DeserializationResult

    fun onPaste()

    fun onPin()
}

context(
    ComposeLifePreferencesProvider,
    LoadedComposeLifePreferencesProvider,
    ComposeLifeDispatchersProvider,
    ClipboardCellStateParserProvider
)
@Composable
fun rememberInlineEditPaneState(
    setSelectionToCellState: (CellState) -> Unit,
): InlineEditPaneState {
    val coroutineScope = rememberCoroutineScope()

    val clipboardWatchingState = rememberClipboardWatchingState(
        coroutineScope = coroutineScope,
        setSelectionToCellState = setSelectionToCellState,
    )

    return remember(coroutineScope, composeLifePreferences, preferences, clipboardWatchingState) {
        object : InlineEditPaneState {
            override val touchToolDropdownOption: ToolDropdownOption get() =
                preferences.touchToolConfig.toToolDropdownOption()

            override fun setTouchToolDropdownOption(toolDropdownOption: ToolDropdownOption) {
                coroutineScope.launch {
                    composeLifePreferences.setTouchToolConfig(toolDropdownOption.toToolConfig())
                }
            }

            override val stylusToolDropdownOption: ToolDropdownOption get() =
                preferences.stylusToolConfig.toToolDropdownOption()

            override fun setStylusToolDropdownOption(toolDropdownOption: ToolDropdownOption) {
                coroutineScope.launch {
                    composeLifePreferences.setStylusToolConfig(toolDropdownOption.toToolConfig())
                }
            }

            override val mouseToolDropdownOption: ToolDropdownOption get() =
                preferences.mouseToolConfig.toToolDropdownOption()

            override fun setMouseToolDropdownOption(toolDropdownOption: ToolDropdownOption) {
                coroutineScope.launch {
                    composeLifePreferences.setMouseToolConfig(toolDropdownOption.toToolConfig())
                }
            }

            override val clipboardWatchingState get() = clipboardWatchingState
        }
    }
}

context(
    ComposeLifePreferencesProvider,
    LoadedComposeLifePreferencesProvider,
    ComposeLifeDispatchersProvider,
    ClipboardCellStateParserProvider
)
@Composable
fun rememberClipboardWatchingState(
    coroutineScope: CoroutineScope = rememberCoroutineScope(),
    setSelectionToCellState: (CellState) -> Unit,
): ClipboardWatchingState =
    if (preferences.completedClipboardWatchingOnboarding) {
        if (preferences.enableClipboardWatching) {
            rememberClipboardWatchingEnabledState(setSelectionToCellState)
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

context(ComposeLifeDispatchersProvider, ClipboardCellStateParserProvider)
@Composable
fun rememberClipboardWatchingEnabledState(
    setSelectionToCellState: (CellState) -> Unit,
): ClipboardWatchingState.ClipboardWatchingEnabled =
    rememberClipboardWatchingEnabledState(
        clipboardReader = rememberClipboardReader(),
        parser = clipboardCellStateParser,
        setSelectionToCellState = setSelectionToCellState,
    )

@Composable
fun rememberClipboardWatchingEnabledState(
    clipboardReader: ClipboardReader,
    parser: ClipboardCellStateParser,
    setSelectionToCellState: (CellState) -> Unit,
): ClipboardWatchingState.ClipboardWatchingEnabled {
    var isLoading by remember { mutableStateOf(false) }
    var currentClipboardCellStateId: UUID by rememberRetained {
        mutableStateOf(UUID.randomUUID())
    }
    var currentDeserializationResult: DeserializationResult? by rememberRetained {
        mutableStateOf(null)
    }
    val previousClipboardCellStates: MutableList<Pair<UUID, DeserializationResult.Successful>> = rememberRetained {
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
                    previousClipboardCellStates.removeLast()
                }

                // We have "locked" in a successful clipboard parsing result into history, so start creating
                // a new one
                currentClipboardCellStateId = UUID.randomUUID()
            }

            // Bring the deserialization result up-to-date
            currentDeserializationResult = newClipboardCellStateResourceState
        }
    }

    return remember(setSelectionToCellState) {
        object : ClipboardWatchingState.ClipboardWatchingEnabled {
            override val isLoading: Boolean
                get() = isLoading

            override val clipboardPreviewStates: List<ClipboardPreviewState>
                get() = listOfNotNull(
                    currentDeserializationResult?.let { deserializationResult ->
                        object : ClipboardPreviewState {
                            override val id = currentClipboardCellStateId
                            override val deserializationResult = deserializationResult

                            override fun onPaste() {
                                when (deserializationResult) {
                                    is DeserializationResult.Successful -> {
                                        setSelectionToCellState(deserializationResult.cellState)
                                    }
                                    is DeserializationResult.Unsuccessful -> Unit
                                }
                            }

                            override fun onPin() {
                                // TODO: Implement clipboard pinning
                            }
                        }
                    },
                ) + previousClipboardCellStates.map { (id, deserializationResult) ->
                    object : ClipboardPreviewState {
                        override val id = id
                        override val deserializationResult = deserializationResult

                        override fun onPaste() {
                            setSelectionToCellState(deserializationResult.cellState)
                        }

                        override fun onPin() {
                            // TODO: Implement clipboard pinning
                        }
                    }
                }
        }
    }
}
