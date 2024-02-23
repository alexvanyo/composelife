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

import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.runComposeUiTest
import com.alexvanyo.composelife.dispatchers.TestComposeLifeDispatchers
import com.alexvanyo.composelife.dispatchers.di.ComposeLifeDispatchersProvider
import com.alexvanyo.composelife.kmpandroidrunner.KmpAndroidJUnit4
import com.alexvanyo.composelife.model.FlexibleCellStateSerializer
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferences
import com.alexvanyo.composelife.preferences.TestComposeLifePreferences
import com.alexvanyo.composelife.preferences.ToolConfig
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.di.LoadedComposeLifePreferencesProvider
import com.alexvanyo.composelife.resourcestate.isSuccess
import com.alexvanyo.composelife.ui.app.ClipboardCellStateParser
import com.alexvanyo.composelife.ui.app.ClipboardCellStateParserProvider
import kotlinx.coroutines.test.StandardTestDispatcher
import kotlinx.coroutines.test.runTest
import org.junit.runner.RunWith
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertIs
import kotlin.test.assertTrue

@OptIn(ExperimentalTestApi::class)
@RunWith(KmpAndroidJUnit4::class)
class InlineEditScreenStateTests {

    @Test
    fun initial_state_is_correct_when_onboarding() = runComposeUiTest {
        runTest {
            val testDispatcher = StandardTestDispatcher(testScheduler)
            val dispatchers = TestComposeLifeDispatchers(testDispatcher, testDispatcher)
            val clipboardCellStateParser = ClipboardCellStateParser(FlexibleCellStateSerializer(dispatchers))
            val composeLifePreferences = TestComposeLifePreferences.Loaded(
                touchToolConfig = ToolConfig.Pan,
                mouseToolConfig = ToolConfig.Select,
                stylusToolConfig = ToolConfig.Draw,
                completedClipboardWatchingOnboarding = false,
                enableClipboardWatching = true,
            )

            lateinit var inlineEditScreenState: InlineEditScreenState

            setContent {
                with(
                    object :
                        ComposeLifeDispatchersProvider,
                        ComposeLifePreferencesProvider,
                        LoadedComposeLifePreferencesProvider,
                        ClipboardCellStateParserProvider {
                        override val dispatchers = dispatchers
                        override val composeLifePreferences = composeLifePreferences
                        override val preferences get(): LoadedComposeLifePreferences {
                            val loadedPreferencesState = composeLifePreferences.loadedPreferencesState
                            assertTrue(loadedPreferencesState.isSuccess())
                            return loadedPreferencesState.value
                        }
                        override val clipboardCellStateParser = clipboardCellStateParser
                    },
                ) {
                    inlineEditScreenState = rememberInlineEditScreenState(
                        setSelectionToCellState = {},
                    )
                }
            }

            assertEquals(
                ToolDropdownOption.Pan,
                inlineEditScreenState.touchToolDropdownOption,
            )
            assertEquals(
                ToolDropdownOption.Draw,
                inlineEditScreenState.stylusToolDropdownOption,
            )
            assertEquals(
                ToolDropdownOption.Select,
                inlineEditScreenState.mouseToolDropdownOption,
            )

            val clipboardWatchingState = inlineEditScreenState.clipboardWatchingState

            assertIs<ClipboardWatchingState.Onboarding>(clipboardWatchingState)
        }
    }

    @Test
    fun allowing_clipboard_watching_updates_state_correctly() = runComposeUiTest {
        runTest {
            val testDispatcher = StandardTestDispatcher(testScheduler)
            val dispatchers = TestComposeLifeDispatchers(testDispatcher, testDispatcher)
            val clipboardCellStateParser = ClipboardCellStateParser(FlexibleCellStateSerializer(dispatchers))
            val composeLifePreferences = TestComposeLifePreferences.Loaded(
                touchToolConfig = ToolConfig.Pan,
                mouseToolConfig = ToolConfig.Select,
                stylusToolConfig = ToolConfig.Draw,
                completedClipboardWatchingOnboarding = false,
                enableClipboardWatching = true,
            )

            lateinit var inlineEditScreenState: InlineEditScreenState

            setContent {
                with(
                    object :
                        ComposeLifeDispatchersProvider,
                        ComposeLifePreferencesProvider,
                        LoadedComposeLifePreferencesProvider,
                        ClipboardCellStateParserProvider {
                        override val dispatchers = dispatchers
                        override val composeLifePreferences = composeLifePreferences
                        override val preferences get(): LoadedComposeLifePreferences {
                            val loadedPreferencesState = composeLifePreferences.loadedPreferencesState
                            assertTrue(loadedPreferencesState.isSuccess())
                            return loadedPreferencesState.value
                        }
                        override val clipboardCellStateParser = clipboardCellStateParser
                    },
                ) {
                    inlineEditScreenState = rememberInlineEditScreenState(
                        setSelectionToCellState = {},
                    )
                }
            }

            val initialClipboardWatchingState = inlineEditScreenState.clipboardWatchingState
            assertIs<ClipboardWatchingState.Onboarding>(initialClipboardWatchingState)

            initialClipboardWatchingState.onAllowClipboardWatching()

            waitForIdle()

            val newPreferencesState = composeLifePreferences.loadedPreferencesState
            assertTrue(newPreferencesState.isSuccess())
            val newPreferences = newPreferencesState.value

            assertTrue(newPreferences.completedClipboardWatchingOnboarding)
            assertTrue(newPreferences.enableClipboardWatching)

            val newClipboardWatchingState = inlineEditScreenState.clipboardWatchingState

            assertIs<ClipboardWatchingState.ClipboardWatchingEnabled>(newClipboardWatchingState)
        }
    }

    @Test
    fun disallowing_clipboard_watching_updates_state_correctly() = runComposeUiTest {
        runTest {
            val testDispatcher = StandardTestDispatcher(testScheduler)
            val dispatchers = TestComposeLifeDispatchers(testDispatcher, testDispatcher)
            val clipboardCellStateParser = ClipboardCellStateParser(FlexibleCellStateSerializer(dispatchers))
            val composeLifePreferences = TestComposeLifePreferences.Loaded(
                touchToolConfig = ToolConfig.Pan,
                mouseToolConfig = ToolConfig.Select,
                stylusToolConfig = ToolConfig.Draw,
                completedClipboardWatchingOnboarding = false,
                enableClipboardWatching = true,
            )

            lateinit var inlineEditScreenState: InlineEditScreenState

            setContent {
                with(
                    object :
                        ComposeLifeDispatchersProvider,
                        ComposeLifePreferencesProvider,
                        LoadedComposeLifePreferencesProvider,
                        ClipboardCellStateParserProvider {
                        override val dispatchers = dispatchers
                        override val composeLifePreferences = composeLifePreferences
                        override val preferences get(): LoadedComposeLifePreferences {
                            val loadedPreferencesState = composeLifePreferences.loadedPreferencesState
                            assertTrue(loadedPreferencesState.isSuccess())
                            return loadedPreferencesState.value
                        }
                        override val clipboardCellStateParser = clipboardCellStateParser
                    },
                ) {
                    inlineEditScreenState = rememberInlineEditScreenState(
                        setSelectionToCellState = {},
                    )
                }
            }

            val initialClipboardWatchingState = inlineEditScreenState.clipboardWatchingState
            assertIs<ClipboardWatchingState.Onboarding>(initialClipboardWatchingState)

            initialClipboardWatchingState.onDisallowClipboardWatching()

            waitForIdle()

            val newPreferencesState = composeLifePreferences.loadedPreferencesState
            assertTrue(newPreferencesState.isSuccess())
            val newPreferences = newPreferencesState.value

            assertTrue(newPreferences.completedClipboardWatchingOnboarding)
            assertFalse(newPreferences.enableClipboardWatching)

            val newClipboardWatchingState = inlineEditScreenState.clipboardWatchingState

            assertIs<ClipboardWatchingState.ClipboardWatchingDisabled>(newClipboardWatchingState)
        }
    }

    @Test
    fun initial_state_is_correct_when_clipboard_watching_enabled() = runComposeUiTest {
        runTest {
            val testDispatcher = StandardTestDispatcher(testScheduler)
            val dispatchers = TestComposeLifeDispatchers(testDispatcher, testDispatcher)
            val clipboardCellStateParser = ClipboardCellStateParser(FlexibleCellStateSerializer(dispatchers))
            val composeLifePreferences = TestComposeLifePreferences.Loaded(
                touchToolConfig = ToolConfig.Pan,
                mouseToolConfig = ToolConfig.Select,
                stylusToolConfig = ToolConfig.Draw,
                completedClipboardWatchingOnboarding = true,
                enableClipboardWatching = true,
            )

            lateinit var inlineEditScreenState: InlineEditScreenState

            setContent {
                with(
                    object :
                        ComposeLifeDispatchersProvider,
                        ComposeLifePreferencesProvider,
                        LoadedComposeLifePreferencesProvider,
                        ClipboardCellStateParserProvider {
                        override val dispatchers = dispatchers
                        override val composeLifePreferences = composeLifePreferences
                        override val preferences get(): LoadedComposeLifePreferences {
                            val loadedPreferencesState = composeLifePreferences.loadedPreferencesState
                            assertTrue(loadedPreferencesState.isSuccess())
                            return loadedPreferencesState.value
                        }
                        override val clipboardCellStateParser = clipboardCellStateParser
                    },
                ) {
                    inlineEditScreenState = rememberInlineEditScreenState(
                        setSelectionToCellState = {},
                    )
                }
            }

            assertEquals(
                ToolDropdownOption.Pan,
                inlineEditScreenState.touchToolDropdownOption,
            )
            assertEquals(
                ToolDropdownOption.Draw,
                inlineEditScreenState.stylusToolDropdownOption,
            )
            assertEquals(
                ToolDropdownOption.Select,
                inlineEditScreenState.mouseToolDropdownOption,
            )

            val clipboardWatchingState = inlineEditScreenState.clipboardWatchingState

            assertIs<ClipboardWatchingState.ClipboardWatchingEnabled>(clipboardWatchingState)
        }
    }

    @Test
    fun initial_state_is_correct_when_clipboard_watching_disabled() = runComposeUiTest {
        runTest {
            val testDispatcher = StandardTestDispatcher(testScheduler)
            val dispatchers = TestComposeLifeDispatchers(testDispatcher, testDispatcher)
            val clipboardCellStateParser = ClipboardCellStateParser(FlexibleCellStateSerializer(dispatchers))
            val composeLifePreferences = TestComposeLifePreferences.Loaded(
                touchToolConfig = ToolConfig.Pan,
                mouseToolConfig = ToolConfig.Select,
                stylusToolConfig = ToolConfig.Draw,
                completedClipboardWatchingOnboarding = true,
                enableClipboardWatching = false,
            )

            lateinit var inlineEditScreenState: InlineEditScreenState

            setContent {
                with(
                    object :
                        ComposeLifeDispatchersProvider,
                        ComposeLifePreferencesProvider,
                        LoadedComposeLifePreferencesProvider,
                        ClipboardCellStateParserProvider {
                        override val dispatchers = dispatchers
                        override val composeLifePreferences = composeLifePreferences
                        override val preferences get(): LoadedComposeLifePreferences {
                            val loadedPreferencesState = composeLifePreferences.loadedPreferencesState
                            assertTrue(loadedPreferencesState.isSuccess())
                            return loadedPreferencesState.value
                        }
                        override val clipboardCellStateParser = clipboardCellStateParser
                    },
                ) {
                    inlineEditScreenState = rememberInlineEditScreenState(
                        setSelectionToCellState = {},
                    )
                }
            }

            assertEquals(
                ToolDropdownOption.Pan,
                inlineEditScreenState.touchToolDropdownOption,
            )
            assertEquals(
                ToolDropdownOption.Draw,
                inlineEditScreenState.stylusToolDropdownOption,
            )
            assertEquals(
                ToolDropdownOption.Select,
                inlineEditScreenState.mouseToolDropdownOption,
            )

            val clipboardWatchingState = inlineEditScreenState.clipboardWatchingState

            assertIs<ClipboardWatchingState.ClipboardWatchingDisabled>(clipboardWatchingState)
        }
    }
}
