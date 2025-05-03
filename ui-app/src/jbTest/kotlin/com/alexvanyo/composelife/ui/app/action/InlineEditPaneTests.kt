/*
 * Copyright 2024 The Android Open Source Project
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

import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.setValue
import androidx.compose.ui.semantics.ProgressBarRangeInfo
import androidx.compose.ui.semantics.SemanticsProperties
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.SemanticsMatcher
import androidx.compose.ui.test.assert
import androidx.compose.ui.test.assertHasClickAction
import androidx.compose.ui.test.hasAnyAncestor
import androidx.compose.ui.test.hasProgressBarRangeInfo
import androidx.compose.ui.test.hasText
import androidx.compose.ui.test.isPopup
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.onNodeWithText
import androidx.compose.ui.test.performClick
import com.alexvanyo.composelife.model.CellStateFormat
import com.alexvanyo.composelife.model.DeserializationResult
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResolver
import com.alexvanyo.composelife.patterns.GliderPattern
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferences
import com.alexvanyo.composelife.preferences.ToolConfig
import com.alexvanyo.composelife.test.BaseUiInjectTest
import com.alexvanyo.composelife.test.runUiTest
import com.alexvanyo.composelife.ui.app.TestComposeLifeApplicationComponent
import com.alexvanyo.composelife.ui.app.TestComposeLifeUiComponent
import com.alexvanyo.composelife.ui.app.TestComposeLifeUiEntryPoint
import com.alexvanyo.composelife.ui.app.createComponent
import com.alexvanyo.composelife.ui.app.kmpGetEntryPoint
import com.alexvanyo.composelife.ui.app.resources.Draw
import com.alexvanyo.composelife.ui.app.resources.Erase
import com.alexvanyo.composelife.ui.app.resources.None
import com.alexvanyo.composelife.ui.app.resources.Pan
import com.alexvanyo.composelife.ui.app.resources.Paste
import com.alexvanyo.composelife.ui.app.resources.Pin
import com.alexvanyo.composelife.ui.app.resources.Select
import com.alexvanyo.composelife.ui.app.resources.Strings
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.uuid.Uuid

@OptIn(ExperimentalTestApi::class)
class InlineEditPaneTests : BaseUiInjectTest<TestComposeLifeApplicationComponent, TestComposeLifeUiComponent>(
    TestComposeLifeApplicationComponent::createComponent,
    TestComposeLifeUiComponent::createComponent,
) {

    private val clipboardCellStatePreviewLocalEntryPoint = object : ClipboardCellStatePreviewLocalEntryPoint {
        override val preferences = LoadedComposeLifePreferences.Defaults
    }

    @OptIn(ExperimentalTestApi::class)
    @Test
    fun clipboard_cell_state_preview_loading_is_displayed_correctly() = runUiTest { uiComponent ->
        val clipboardCellStatePreviewInjectEntryPoint: ClipboardCellStatePreviewInjectEntryPoint =
            uiComponent.kmpGetEntryPoint<TestComposeLifeUiEntryPoint>()

        setContent {
            with(
                object :
                    ClipboardCellStatePreviewInjectEntryPoint by clipboardCellStatePreviewInjectEntryPoint,
                    ClipboardCellStatePreviewLocalEntryPoint by clipboardCellStatePreviewLocalEntryPoint {},
            ) {
                InlineEditPane(
                    state = object : InlineEditPaneState {
                        override val touchToolConfig = ToolConfig.Pan

                        override fun setTouchToolConfig(toolConfig: ToolConfig) = Unit

                        override val stylusToolConfig = ToolConfig.None

                        override fun setStylusToolConfig(toolConfig: ToolConfig) = Unit

                        override val mouseToolConfig = ToolConfig.None

                        override fun setMouseToolConfig(toolConfig: ToolConfig) = Unit

                        override val clipboardWatchingState: ClipboardWatchingState
                            get() = object : ClipboardWatchingState.ClipboardWatchingEnabled {
                                override val useSharedElementForCellStatePreviews = false
                                override val isLoading = true

                                override val clipboardPreviewStates: List<ClipboardPreviewState> = emptyList()

                                override val pinnedClipboardPreviewStates: List<PinnedClipboardPreviewState> =
                                    emptyList()
                            }
                    },
                )
            }
        }

        onNode(SemanticsMatcher.keyIsDefined(SemanticsProperties.ProgressBarRangeInfo))
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo.Indeterminate))
    }

    @Test
    fun clipboard_cell_state_preview_success_is_displayed_correctly() = runUiTest { uiComponent ->
        val clipboardCellStatePreviewInjectEntryPoint: ClipboardCellStatePreviewInjectEntryPoint =
            uiComponent.kmpGetEntryPoint<TestComposeLifeUiEntryPoint>()

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            with(
                object :
                    ClipboardCellStatePreviewInjectEntryPoint by clipboardCellStatePreviewInjectEntryPoint,
                    ClipboardCellStatePreviewLocalEntryPoint by clipboardCellStatePreviewLocalEntryPoint {},
            ) {
                val clipboardPreviewStates = remember {
                    listOf(
                        object : ClipboardPreviewState {
                            override val id = Uuid.random()
                            override val deserializationResult = DeserializationResult.Successful(
                                warnings = emptyList(),
                                cellState = GliderPattern.seedCellState,
                                format = CellStateFormat.FixedFormat.Plaintext,
                            )

                            override val isPinned = false

                            override fun onPaste() = Unit

                            override fun onPinChanged() = Unit

                            override fun onViewDeserializationInfo() = Unit
                        },
                    )
                }

                InlineEditPane(
                    state = object : InlineEditPaneState {
                        override val touchToolConfig = ToolConfig.Pan

                        override fun setTouchToolConfig(toolConfig: ToolConfig) = Unit

                        override val stylusToolConfig = ToolConfig.None

                        override fun setStylusToolConfig(toolConfig: ToolConfig) = Unit

                        override val mouseToolConfig = ToolConfig.None

                        override fun setMouseToolConfig(toolConfig: ToolConfig) = Unit

                        override val clipboardWatchingState: ClipboardWatchingState
                            get() = object : ClipboardWatchingState.ClipboardWatchingEnabled {
                                override val useSharedElementForCellStatePreviews = false
                                override val isLoading = false

                                override val clipboardPreviewStates = clipboardPreviewStates

                                override val pinnedClipboardPreviewStates: List<PinnedClipboardPreviewState> =
                                    emptyList()
                            }
                    },
                )
            }
        }

        onNode(SemanticsMatcher.keyIsDefined(SemanticsProperties.ProgressBarRangeInfo))
            .assertDoesNotExist()

        onNodeWithContentDescription(resolver(Strings.Paste))
            .assertExists()
            .assertHasClickAction()

        onNodeWithContentDescription(resolver(Strings.Pin))
            .assertExists()
            .assertHasClickAction()
    }

    @Test
    fun clipboard_cell_state_preview_success_paste_is_handled_correctly() = runUiTest { uiComponent ->
        val clipboardCellStatePreviewInjectEntryPoint: ClipboardCellStatePreviewInjectEntryPoint =
            uiComponent.kmpGetEntryPoint<TestComposeLifeUiEntryPoint>()

        lateinit var resolver: (ParameterizedString) -> String

        var onPasteClipboardClickedCount = 0

        setContent {
            resolver = parameterizedStringResolver()
            with(
                object :
                    ClipboardCellStatePreviewInjectEntryPoint by clipboardCellStatePreviewInjectEntryPoint,
                    ClipboardCellStatePreviewLocalEntryPoint by clipboardCellStatePreviewLocalEntryPoint {},
            ) {
                val clipboardPreviewStates = remember {
                    listOf(
                        object : ClipboardPreviewState {
                            override val id = Uuid.random()
                            override val deserializationResult = DeserializationResult.Successful(
                                warnings = emptyList(),
                                cellState = GliderPattern.seedCellState,
                                format = CellStateFormat.FixedFormat.Plaintext,
                            )

                            override val isPinned = false

                            override fun onPaste() {
                                onPasteClipboardClickedCount++
                            }

                            override fun onPinChanged() = Unit

                            override fun onViewDeserializationInfo() = Unit
                        },
                    )
                }

                InlineEditPane(
                    state = object : InlineEditPaneState {
                        override val touchToolConfig = ToolConfig.Pan

                        override fun setTouchToolConfig(toolConfig: ToolConfig) = Unit

                        override val stylusToolConfig = ToolConfig.None

                        override fun setStylusToolConfig(toolConfig: ToolConfig) = Unit

                        override val mouseToolConfig = ToolConfig.None

                        override fun setMouseToolConfig(toolConfig: ToolConfig) = Unit

                        override val clipboardWatchingState: ClipboardWatchingState
                            get() = object : ClipboardWatchingState.ClipboardWatchingEnabled {
                                override val useSharedElementForCellStatePreviews = false
                                override val isLoading = false

                                override val clipboardPreviewStates = clipboardPreviewStates

                                override val pinnedClipboardPreviewStates: List<PinnedClipboardPreviewState> =
                                    emptyList()
                            }
                    },
                )
            }
        }

        onNodeWithContentDescription(resolver(Strings.Paste))
            .performClick()

        assertEquals(1, onPasteClipboardClickedCount)
    }

    @Test
    fun clipboard_cell_state_preview_success_pin_is_handled_correctly() = runUiTest { uiComponent ->
        val clipboardCellStatePreviewInjectEntryPoint: ClipboardCellStatePreviewInjectEntryPoint =
            uiComponent.kmpGetEntryPoint<TestComposeLifeUiEntryPoint>()

        lateinit var resolver: (ParameterizedString) -> String

        var onPinClipboardClickedCount = 0

        setContent {
            resolver = parameterizedStringResolver()
            with(
                object :
                    ClipboardCellStatePreviewInjectEntryPoint by clipboardCellStatePreviewInjectEntryPoint,
                    ClipboardCellStatePreviewLocalEntryPoint by clipboardCellStatePreviewLocalEntryPoint {},
            ) {
                val clipboardPreviewStates = remember {
                    listOf(
                        object : ClipboardPreviewState {
                            override val id = Uuid.random()
                            override val deserializationResult = DeserializationResult.Successful(
                                warnings = emptyList(),
                                cellState = GliderPattern.seedCellState,
                                format = CellStateFormat.FixedFormat.Plaintext,
                            )
                            override val isPinned = false

                            override fun onPaste() = Unit

                            override fun onPinChanged() {
                                onPinClipboardClickedCount++
                            }

                            override fun onViewDeserializationInfo() = Unit
                        },
                    )
                }

                InlineEditPane(
                    state = object : InlineEditPaneState {
                        override val touchToolConfig = ToolConfig.Pan

                        override fun setTouchToolConfig(toolConfig: ToolConfig) = Unit

                        override val stylusToolConfig = ToolConfig.None

                        override fun setStylusToolConfig(toolConfig: ToolConfig) = Unit

                        override val mouseToolConfig = ToolConfig.None

                        override fun setMouseToolConfig(toolConfig: ToolConfig) = Unit

                        override val clipboardWatchingState: ClipboardWatchingState
                            get() = object : ClipboardWatchingState.ClipboardWatchingEnabled {
                                override val useSharedElementForCellStatePreviews = false
                                override val isLoading = false

                                override val clipboardPreviewStates = clipboardPreviewStates

                                override val pinnedClipboardPreviewStates: List<PinnedClipboardPreviewState> =
                                    emptyList()
                            }
                    },
                )
            }
        }

        onNodeWithContentDescription(resolver(Strings.Pin))
            .performClick()

        assertEquals(1, onPinClipboardClickedCount)
    }

    @Test
    fun touch_config_pan_is_displayed_correctly() = runUiTest { uiComponent ->
        val clipboardCellStatePreviewInjectEntryPoint: ClipboardCellStatePreviewInjectEntryPoint =
            uiComponent.kmpGetEntryPoint<TestComposeLifeUiEntryPoint>()

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            with(
                object :
                    ClipboardCellStatePreviewInjectEntryPoint by clipboardCellStatePreviewInjectEntryPoint,
                    ClipboardCellStatePreviewLocalEntryPoint by clipboardCellStatePreviewLocalEntryPoint {},
            ) {
                InlineEditPane(
                    state = object : InlineEditPaneState {
                        override val touchToolConfig = ToolConfig.Pan

                        override fun setTouchToolConfig(toolConfig: ToolConfig) = Unit

                        override val stylusToolConfig = ToolConfig.None

                        override fun setStylusToolConfig(toolConfig: ToolConfig) = Unit

                        override val mouseToolConfig = ToolConfig.None

                        override fun setMouseToolConfig(toolConfig: ToolConfig) = Unit

                        override val clipboardWatchingState: ClipboardWatchingState
                            get() = object : ClipboardWatchingState.ClipboardWatchingEnabled {
                                override val useSharedElementForCellStatePreviews = false
                                override val isLoading = true

                                override val clipboardPreviewStates: List<ClipboardPreviewState> = emptyList()

                                override val pinnedClipboardPreviewStates: List<PinnedClipboardPreviewState> =
                                    emptyList()
                            }
                    },
                )
            }
        }

        onNodeWithText(resolver(Strings.Pan))
            .assertExists()
            .assertHasClickAction()
    }

    @Test
    fun touch_config_draw_is_displayed_correctly() = runUiTest { uiComponent ->
        val clipboardCellStatePreviewInjectEntryPoint: ClipboardCellStatePreviewInjectEntryPoint =
            uiComponent.kmpGetEntryPoint<TestComposeLifeUiEntryPoint>()

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            with(
                object :
                    ClipboardCellStatePreviewInjectEntryPoint by clipboardCellStatePreviewInjectEntryPoint,
                    ClipboardCellStatePreviewLocalEntryPoint by clipboardCellStatePreviewLocalEntryPoint {},
            ) {
                InlineEditPane(
                    state = object : InlineEditPaneState {
                        override val touchToolConfig = ToolConfig.Draw

                        override fun setTouchToolConfig(toolConfig: ToolConfig) = Unit

                        override val stylusToolConfig = ToolConfig.None

                        override fun setStylusToolConfig(toolConfig: ToolConfig) = Unit

                        override val mouseToolConfig = ToolConfig.None

                        override fun setMouseToolConfig(toolConfig: ToolConfig) = Unit

                        override val clipboardWatchingState: ClipboardWatchingState
                            get() = object : ClipboardWatchingState.ClipboardWatchingEnabled {
                                override val useSharedElementForCellStatePreviews = false
                                override val isLoading = true

                                override val clipboardPreviewStates: List<ClipboardPreviewState> = emptyList()

                                override val pinnedClipboardPreviewStates: List<PinnedClipboardPreviewState> =
                                    emptyList()
                            }
                    },
                )
            }
        }

        onNodeWithText(resolver(Strings.Draw))
            .assertExists()
            .assertHasClickAction()
    }

    @Test
    fun touch_config_erase_is_displayed_correctly() = runUiTest { uiComponent ->
        val clipboardCellStatePreviewInjectEntryPoint: ClipboardCellStatePreviewInjectEntryPoint =
            uiComponent.kmpGetEntryPoint<TestComposeLifeUiEntryPoint>()

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            with(
                object :
                    ClipboardCellStatePreviewInjectEntryPoint by clipboardCellStatePreviewInjectEntryPoint,
                    ClipboardCellStatePreviewLocalEntryPoint by clipboardCellStatePreviewLocalEntryPoint {},
            ) {
                InlineEditPane(
                    state = object : InlineEditPaneState {
                        override val touchToolConfig = ToolConfig.Erase

                        override fun setTouchToolConfig(toolConfig: ToolConfig) = Unit

                        override val stylusToolConfig = ToolConfig.None

                        override fun setStylusToolConfig(toolConfig: ToolConfig) = Unit

                        override val mouseToolConfig = ToolConfig.None

                        override fun setMouseToolConfig(toolConfig: ToolConfig) = Unit

                        override val clipboardWatchingState: ClipboardWatchingState
                            get() = object : ClipboardWatchingState.ClipboardWatchingEnabled {
                                override val useSharedElementForCellStatePreviews = false
                                override val isLoading = true

                                override val clipboardPreviewStates: List<ClipboardPreviewState> = emptyList()

                                override val pinnedClipboardPreviewStates: List<PinnedClipboardPreviewState> =
                                    emptyList()
                            }
                    },
                )
            }
        }

        onNodeWithText(resolver(Strings.Erase))
            .assertExists()
            .assertHasClickAction()
    }

    @Test
    fun touch_config_select_is_displayed_correctly() = runUiTest { uiComponent ->
        val clipboardCellStatePreviewInjectEntryPoint: ClipboardCellStatePreviewInjectEntryPoint =
            uiComponent.kmpGetEntryPoint<TestComposeLifeUiEntryPoint>()

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            with(
                object :
                    ClipboardCellStatePreviewInjectEntryPoint by clipboardCellStatePreviewInjectEntryPoint,
                    ClipboardCellStatePreviewLocalEntryPoint by clipboardCellStatePreviewLocalEntryPoint {},
            ) {
                InlineEditPane(
                    state = object : InlineEditPaneState {
                        override val touchToolConfig = ToolConfig.Select

                        override fun setTouchToolConfig(toolConfig: ToolConfig) = Unit

                        override val stylusToolConfig = ToolConfig.None

                        override fun setStylusToolConfig(toolConfig: ToolConfig) = Unit

                        override val mouseToolConfig = ToolConfig.None

                        override fun setMouseToolConfig(toolConfig: ToolConfig) = Unit

                        override val clipboardWatchingState: ClipboardWatchingState
                            get() = object : ClipboardWatchingState.ClipboardWatchingEnabled {
                                override val useSharedElementForCellStatePreviews = false
                                override val isLoading = true

                                override val clipboardPreviewStates: List<ClipboardPreviewState> = emptyList()

                                override val pinnedClipboardPreviewStates: List<PinnedClipboardPreviewState> =
                                    emptyList()
                            }
                    },
                )
            }
        }

        onNodeWithText(resolver(Strings.Select))
            .assertExists()
            .assertHasClickAction()
    }

    @Test
    fun touch_config_none_is_displayed_correctly() = runUiTest { uiComponent ->
        val clipboardCellStatePreviewInjectEntryPoint: ClipboardCellStatePreviewInjectEntryPoint =
            uiComponent.kmpGetEntryPoint<TestComposeLifeUiEntryPoint>()

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            with(
                object :
                    ClipboardCellStatePreviewInjectEntryPoint by clipboardCellStatePreviewInjectEntryPoint,
                    ClipboardCellStatePreviewLocalEntryPoint by clipboardCellStatePreviewLocalEntryPoint {},
            ) {
                InlineEditPane(
                    state = object : InlineEditPaneState {
                        override val touchToolConfig = ToolConfig.None

                        override fun setTouchToolConfig(toolConfig: ToolConfig) = Unit

                        override val stylusToolConfig = ToolConfig.Draw

                        override fun setStylusToolConfig(toolConfig: ToolConfig) = Unit

                        override val mouseToolConfig = ToolConfig.Draw

                        override fun setMouseToolConfig(toolConfig: ToolConfig) = Unit

                        override val clipboardWatchingState: ClipboardWatchingState
                            get() = object : ClipboardWatchingState.ClipboardWatchingEnabled {
                                override val useSharedElementForCellStatePreviews = false
                                override val isLoading = true

                                override val clipboardPreviewStates: List<ClipboardPreviewState> = emptyList()

                                override val pinnedClipboardPreviewStates: List<PinnedClipboardPreviewState> =
                                    emptyList()
                            }
                    },
                )
            }
        }

        onNodeWithText(resolver(Strings.None))
            .assertExists()
            .assertHasClickAction()
    }

    @Test
    fun touch_config_popup_displays_options() = runUiTest { uiComponent ->
        val clipboardCellStatePreviewInjectEntryPoint: ClipboardCellStatePreviewInjectEntryPoint =
            uiComponent.kmpGetEntryPoint<TestComposeLifeUiEntryPoint>()

        var touchToolConfig: ToolConfig by mutableStateOf(ToolConfig.Pan)

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            with(
                object :
                    ClipboardCellStatePreviewInjectEntryPoint by clipboardCellStatePreviewInjectEntryPoint,
                    ClipboardCellStatePreviewLocalEntryPoint by clipboardCellStatePreviewLocalEntryPoint {},
            ) {
                InlineEditPane(
                    state = object : InlineEditPaneState {
                        override val touchToolConfig get() = touchToolConfig

                        override fun setTouchToolConfig(toolConfig: ToolConfig) {
                            touchToolConfig = toolConfig
                        }

                        override val stylusToolConfig = ToolConfig.None

                        override fun setStylusToolConfig(toolConfig: ToolConfig) = Unit

                        override val mouseToolConfig = ToolConfig.None

                        override fun setMouseToolConfig(toolConfig: ToolConfig) = Unit

                        override val clipboardWatchingState: ClipboardWatchingState
                            get() = object : ClipboardWatchingState.ClipboardWatchingEnabled {
                                override val useSharedElementForCellStatePreviews = false
                                override val isLoading = true

                                override val clipboardPreviewStates: List<ClipboardPreviewState> = emptyList()

                                override val pinnedClipboardPreviewStates: List<PinnedClipboardPreviewState> =
                                    emptyList()
                            }
                    },
                )
            }
        }

        onNodeWithText(resolver(Strings.Pan))
            .performClick()

        onNode(hasAnyAncestor(isPopup()) and hasText(resolver(Strings.Draw)))
            .assertHasClickAction()
            .performClick()

        assertEquals(ToolConfig.Draw, touchToolConfig)

        onNode(isPopup())
            .assertDoesNotExist()

        onNodeWithText(resolver(Strings.Draw))
            .assertExists()
            .assertHasClickAction()
    }
}
