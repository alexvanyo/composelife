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
import com.alexvanyo.composelife.kmpandroidrunner.KmpAndroidJUnit4
import com.alexvanyo.composelife.model.CellStateFormat
import com.alexvanyo.composelife.model.DeserializationResult
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResolver
import com.alexvanyo.composelife.patterns.GliderPattern
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferences
import com.alexvanyo.composelife.test.BaseUiInjectTest2
import com.alexvanyo.composelife.test.runUiTest
import com.alexvanyo.composelife.ui.app.TestComposeLifeApplicationComponent
import com.alexvanyo.composelife.ui.app.TestComposeLifeUiComponent
import com.alexvanyo.composelife.ui.app.createComponent
import com.alexvanyo.composelife.ui.app.resources.Draw
import com.alexvanyo.composelife.ui.app.resources.Erase
import com.alexvanyo.composelife.ui.app.resources.None
import com.alexvanyo.composelife.ui.app.resources.Pan
import com.alexvanyo.composelife.ui.app.resources.Paste
import com.alexvanyo.composelife.ui.app.resources.Pin
import com.alexvanyo.composelife.ui.app.resources.Select
import com.alexvanyo.composelife.ui.app.resources.Strings
import com.benasher44.uuid.uuid4
import org.junit.runner.RunWith
import kotlin.test.Test
import kotlin.test.assertEquals

@OptIn(ExperimentalTestApi::class)
@RunWith(KmpAndroidJUnit4::class)
class InlineEditPaneTests : BaseUiInjectTest2<TestComposeLifeApplicationComponent, TestComposeLifeUiComponent>(
    TestComposeLifeApplicationComponent::createComponent,
    TestComposeLifeUiComponent::createComponent,
) {

    private val clipboardCellStatePreviewLocalEntryPoint = object : ClipboardCellStatePreviewLocalEntryPoint {
        override val preferences = LoadedComposeLifePreferences.Defaults
    }

    @OptIn(ExperimentalTestApi::class)
    @Test
    fun clipboard_cell_state_preview_loading_is_displayed_correctly() = runUiTest {
        val clipboardCellStatePreviewInjectEntryPoint: ClipboardCellStatePreviewInjectEntryPoint =
            uiComponent.entryPoint

        setContent {
            with(
                object :
                    ClipboardCellStatePreviewInjectEntryPoint by clipboardCellStatePreviewInjectEntryPoint,
                    ClipboardCellStatePreviewLocalEntryPoint by clipboardCellStatePreviewLocalEntryPoint {},
            ) {
                InlineEditPane(
                    state = object : InlineEditPaneState {
                        override val touchToolDropdownOption = ToolDropdownOption.Pan

                        override fun setTouchToolDropdownOption(toolDropdownOption: ToolDropdownOption) = Unit

                        override val stylusToolDropdownOption = ToolDropdownOption.None

                        override fun setStylusToolDropdownOption(toolDropdownOption: ToolDropdownOption) = Unit

                        override val mouseToolDropdownOption = ToolDropdownOption.None

                        override fun setMouseToolDropdownOption(toolDropdownOption: ToolDropdownOption) = Unit

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
    fun clipboard_cell_state_preview_success_is_displayed_correctly() = runUiTest {
        val clipboardCellStatePreviewInjectEntryPoint: ClipboardCellStatePreviewInjectEntryPoint =
            uiComponent.entryPoint

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
                            override val id = uuid4()
                            override val deserializationResult = DeserializationResult.Successful(
                                warnings = emptyList(),
                                cellState = GliderPattern.seedCellState,
                                format = CellStateFormat.FixedFormat.Plaintext,
                            )

                            override val isPinned = false

                            override fun onPaste() = Unit

                            override fun onPinChanged() = Unit
                        },
                    )
                }

                InlineEditPane(
                    state = object : InlineEditPaneState {
                        override val touchToolDropdownOption = ToolDropdownOption.Pan

                        override fun setTouchToolDropdownOption(toolDropdownOption: ToolDropdownOption) = Unit

                        override val stylusToolDropdownOption = ToolDropdownOption.None

                        override fun setStylusToolDropdownOption(toolDropdownOption: ToolDropdownOption) = Unit

                        override val mouseToolDropdownOption = ToolDropdownOption.None

                        override fun setMouseToolDropdownOption(toolDropdownOption: ToolDropdownOption) = Unit

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
    fun clipboard_cell_state_preview_success_paste_is_handled_correctly() = runUiTest {
        val clipboardCellStatePreviewInjectEntryPoint: ClipboardCellStatePreviewInjectEntryPoint =
            uiComponent.entryPoint

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
                            override val id = uuid4()
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
                        },
                    )
                }

                InlineEditPane(
                    state = object : InlineEditPaneState {
                        override val touchToolDropdownOption = ToolDropdownOption.Pan

                        override fun setTouchToolDropdownOption(toolDropdownOption: ToolDropdownOption) = Unit

                        override val stylusToolDropdownOption = ToolDropdownOption.None

                        override fun setStylusToolDropdownOption(toolDropdownOption: ToolDropdownOption) = Unit

                        override val mouseToolDropdownOption = ToolDropdownOption.None

                        override fun setMouseToolDropdownOption(toolDropdownOption: ToolDropdownOption) = Unit

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
    fun clipboard_cell_state_preview_success_pin_is_handled_correctly() = runUiTest {
        val clipboardCellStatePreviewInjectEntryPoint: ClipboardCellStatePreviewInjectEntryPoint =
            uiComponent.entryPoint

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
                            override val id = uuid4()
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
                        },
                    )
                }

                InlineEditPane(
                    state = object : InlineEditPaneState {
                        override val touchToolDropdownOption = ToolDropdownOption.Pan

                        override fun setTouchToolDropdownOption(toolDropdownOption: ToolDropdownOption) = Unit

                        override val stylusToolDropdownOption = ToolDropdownOption.None

                        override fun setStylusToolDropdownOption(toolDropdownOption: ToolDropdownOption) = Unit

                        override val mouseToolDropdownOption = ToolDropdownOption.None

                        override fun setMouseToolDropdownOption(toolDropdownOption: ToolDropdownOption) = Unit

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
    fun touch_config_pan_is_displayed_correctly() = runUiTest {
        val clipboardCellStatePreviewInjectEntryPoint: ClipboardCellStatePreviewInjectEntryPoint =
            uiComponent.entryPoint

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
                        override val touchToolDropdownOption = ToolDropdownOption.Pan

                        override fun setTouchToolDropdownOption(toolDropdownOption: ToolDropdownOption) = Unit

                        override val stylusToolDropdownOption = ToolDropdownOption.None

                        override fun setStylusToolDropdownOption(toolDropdownOption: ToolDropdownOption) = Unit

                        override val mouseToolDropdownOption = ToolDropdownOption.None

                        override fun setMouseToolDropdownOption(toolDropdownOption: ToolDropdownOption) = Unit

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
    fun touch_config_draw_is_displayed_correctly() = runUiTest {
        val clipboardCellStatePreviewInjectEntryPoint: ClipboardCellStatePreviewInjectEntryPoint =
            uiComponent.entryPoint

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
                        override val touchToolDropdownOption = ToolDropdownOption.Draw

                        override fun setTouchToolDropdownOption(toolDropdownOption: ToolDropdownOption) = Unit

                        override val stylusToolDropdownOption = ToolDropdownOption.None

                        override fun setStylusToolDropdownOption(toolDropdownOption: ToolDropdownOption) = Unit

                        override val mouseToolDropdownOption = ToolDropdownOption.None

                        override fun setMouseToolDropdownOption(toolDropdownOption: ToolDropdownOption) = Unit

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
    fun touch_config_erase_is_displayed_correctly() = runUiTest {
        val clipboardCellStatePreviewInjectEntryPoint: ClipboardCellStatePreviewInjectEntryPoint =
            uiComponent.entryPoint

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
                        override val touchToolDropdownOption = ToolDropdownOption.Erase

                        override fun setTouchToolDropdownOption(toolDropdownOption: ToolDropdownOption) = Unit

                        override val stylusToolDropdownOption = ToolDropdownOption.None

                        override fun setStylusToolDropdownOption(toolDropdownOption: ToolDropdownOption) = Unit

                        override val mouseToolDropdownOption = ToolDropdownOption.None

                        override fun setMouseToolDropdownOption(toolDropdownOption: ToolDropdownOption) = Unit

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
    fun touch_config_select_is_displayed_correctly() = runUiTest {
        val clipboardCellStatePreviewInjectEntryPoint: ClipboardCellStatePreviewInjectEntryPoint =
            uiComponent.entryPoint

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
                        override val touchToolDropdownOption = ToolDropdownOption.Select

                        override fun setTouchToolDropdownOption(toolDropdownOption: ToolDropdownOption) = Unit

                        override val stylusToolDropdownOption = ToolDropdownOption.None

                        override fun setStylusToolDropdownOption(toolDropdownOption: ToolDropdownOption) = Unit

                        override val mouseToolDropdownOption = ToolDropdownOption.None

                        override fun setMouseToolDropdownOption(toolDropdownOption: ToolDropdownOption) = Unit

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
    fun touch_config_none_is_displayed_correctly() = runUiTest {
        val clipboardCellStatePreviewInjectEntryPoint: ClipboardCellStatePreviewInjectEntryPoint =
            uiComponent.entryPoint

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
                        override val touchToolDropdownOption = ToolDropdownOption.None

                        override fun setTouchToolDropdownOption(toolDropdownOption: ToolDropdownOption) = Unit

                        override val stylusToolDropdownOption = ToolDropdownOption.Draw

                        override fun setStylusToolDropdownOption(toolDropdownOption: ToolDropdownOption) = Unit

                        override val mouseToolDropdownOption = ToolDropdownOption.Draw

                        override fun setMouseToolDropdownOption(toolDropdownOption: ToolDropdownOption) = Unit

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
    fun touch_config_popup_displays_options() = runUiTest {
        val clipboardCellStatePreviewInjectEntryPoint: ClipboardCellStatePreviewInjectEntryPoint =
            uiComponent.entryPoint

        var touchToolDropdownOption: ToolDropdownOption by mutableStateOf(ToolDropdownOption.Pan)

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
                        override val touchToolDropdownOption get() = touchToolDropdownOption

                        override fun setTouchToolDropdownOption(toolDropdownOption: ToolDropdownOption) {
                            touchToolDropdownOption = toolDropdownOption
                        }

                        override val stylusToolDropdownOption = ToolDropdownOption.None

                        override fun setStylusToolDropdownOption(toolDropdownOption: ToolDropdownOption) = Unit

                        override val mouseToolDropdownOption = ToolDropdownOption.None

                        override fun setMouseToolDropdownOption(toolDropdownOption: ToolDropdownOption) = Unit

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

        assertEquals(ToolDropdownOption.Draw, touchToolDropdownOption)

        onNode(isPopup())
            .assertDoesNotExist()

        onNodeWithText(resolver(Strings.Draw))
            .assertExists()
            .assertHasClickAction()
    }
}
