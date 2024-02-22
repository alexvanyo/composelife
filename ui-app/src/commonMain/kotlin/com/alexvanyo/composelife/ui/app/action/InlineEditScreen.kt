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
import androidx.compose.runtime.getValue
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
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
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.resourcestate.asResourceState
import com.alexvanyo.composelife.resourcestate.collectAsState
import com.alexvanyo.composelife.resourcestate.isSuccess
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
import com.alexvanyo.composelife.ui.util.clipboardStateKey
import com.alexvanyo.composelife.ui.util.rememberClipboardReader
import com.livefront.sealedenum.GenSealedEnum
import kotlinx.collections.immutable.toImmutableList
import kotlinx.coroutines.flow.flow
import kotlinx.coroutines.launch

interface InlineEditScreenInjectEntryPoint :
    ComposeLifePreferencesProvider,
    ComposeLifeDispatchersProvider,
    ClipboardCellStateParserProvider,
    ClipboardCellStatePreviewInjectEntryPoint

interface InlineEditScreenLocalEntryPoint :
    LoadedComposeLifePreferencesProvider,
    ClipboardCellStatePreviewLocalEntryPoint

context(InlineEditScreenInjectEntryPoint, InlineEditScreenLocalEntryPoint)
@Composable
fun InlineEditScreen(
    setSelectionToCellState: (CellState) -> Unit,
    modifier: Modifier = Modifier,
    scrollState: ScrollState = rememberScrollState(),
) = InlineEditScreen(
    state = rememberInlineEditScreenState(setSelectionToCellState),
    modifier = modifier,
    scrollState = scrollState,
)

context(ClipboardCellStatePreviewInjectEntryPoint, ClipboardCellStatePreviewLocalEntryPoint)
@Suppress("LongParameterList", "LongMethod")
@Composable
fun InlineEditScreen(
    state: InlineEditScreenState,
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

interface InlineEditScreenState {
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

        val clipboardCellStateResourceState: ResourceState<DeserializationResult>

        fun onPasteClipboard()

        fun onPinClipboard()
    }
}

context(
    ComposeLifePreferencesProvider,
    LoadedComposeLifePreferencesProvider,
    ComposeLifeDispatchersProvider,
    ClipboardCellStateParserProvider
)
@Composable
fun rememberInlineEditScreenState(
    setSelectionToCellState: (CellState) -> Unit,
): InlineEditScreenState {
    val coroutineScope = rememberCoroutineScope()

    val clipboardWatchingState = if (preferences.completedClipboardWatchingOnboarding) {
        if (preferences.enableClipboardWatching) {
            val clipboardReader = rememberClipboardReader()
            val parser: ClipboardCellStateParser = clipboardCellStateParser

            val clipboardCellStateResourceState: ResourceState<DeserializationResult> by
                remember(clipboardReader, clipboardReader.clipboardStateKey, parser) {
                    flow { emit(parser.parseCellState(clipboardReader)) }.asResourceState()
                }
                    .collectAsState()

            remember(setSelectionToCellState) {
                object : ClipboardWatchingState.ClipboardWatchingEnabled {
                    override val clipboardCellStateResourceState get() = clipboardCellStateResourceState

                    override fun onPasteClipboard() {
                        val clipboardResourceState = clipboardCellStateResourceState
                        if (clipboardResourceState.isSuccess()) {
                            when (val clipboardDeserializationResult = clipboardResourceState.value) {
                                is DeserializationResult.Successful -> {
                                    setSelectionToCellState(clipboardDeserializationResult.cellState)
                                }
                                is DeserializationResult.Unsuccessful -> Unit
                            }
                        }
                    }

                    override fun onPinClipboard() {
                        // TODO: Implement clipboard pinning
                    }
                }
            }
        } else {
            ClipboardWatchingState.ClipboardWatchingDisabled
        }
    } else {
        remember(coroutineScope, composeLifePreferences) {
            object : ClipboardWatchingState.Onboarding {
                override fun onAllowClipboardWatching() {
                    coroutineScope.launch {
                        composeLifePreferences.setEnableClipboardWatching(true)
                        composeLifePreferences.setCompletedClipboardWatchingOnboarding(true)
                    }
                }

                override fun onDisallowClipboardWatching() {
                    coroutineScope.launch {
                        composeLifePreferences.setEnableClipboardWatching(false)
                        composeLifePreferences.setCompletedClipboardWatchingOnboarding(true)
                    }
                }
            }
        }
    }

    return remember(coroutineScope, composeLifePreferences, preferences, clipboardWatchingState) {
        object : InlineEditScreenState {
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
