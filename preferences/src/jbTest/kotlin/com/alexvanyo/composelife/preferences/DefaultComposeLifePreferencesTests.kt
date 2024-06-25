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

package com.alexvanyo.composelife.preferences

import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.resourcestate.isSuccess
import com.alexvanyo.composelife.sessionvalue.SessionValue
import kotlinx.coroutines.delay
import kotlinx.coroutines.launch
import kotlinx.coroutines.test.TestScope
import kotlinx.coroutines.test.runTest
import okio.Path.Companion.toPath
import okio.fakefilesystem.FakeFileSystem
import java.util.UUID
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertIs
import kotlin.test.assertNotNull
import kotlin.test.assertTrue
import kotlin.time.Duration.Companion.milliseconds

@Suppress("LargeClass")
class DefaultComposeLifePreferencesTests {

    private fun runPreferencesTest(testBody: suspend TestScope.(ComposeLifePreferences) -> Unit) = runTest {
        val composelifePreferences = DefaultComposeLifePreferences(
            DiskPreferencesDataStore(
                fileSystem = FakeFileSystem(),
                path = lazy { "/preferences.pb".toPath() },
                scope = backgroundScope,
            ),
        )
        backgroundScope.launch {
            composelifePreferences.update()
        }
        testBody(composelifePreferences)
    }

    @Test
    fun default_loaded_preferences_is_correct() = runPreferencesTest { composelifePreferences ->
        assertEquals(ResourceState.Loading, composelifePreferences.loadedPreferencesState)

        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(LoadedComposeLifePreferences.Defaults),
            composelifePreferences.loadedPreferencesState,
        )
    }

    @Test
    fun default_algorithm_choice_is_hashlife() = runPreferencesTest { composelifePreferences ->
        assertEquals(ResourceState.Loading, composelifePreferences.algorithmChoiceState)

        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(AlgorithmType.HashLifeAlgorithm),
            composelifePreferences.algorithmChoiceState,
        )
    }

    @Test
    fun setting_algorithm_choice_updates_value() = runPreferencesTest { composelifePreferences ->
        assertEquals(ResourceState.Loading, composelifePreferences.algorithmChoiceState)

        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(AlgorithmType.HashLifeAlgorithm),
            composelifePreferences.algorithmChoiceState,
        )

        composelifePreferences.setAlgorithmChoice(AlgorithmType.NaiveAlgorithm)
        delay(1.milliseconds)

        assertEquals(ResourceState.Success(AlgorithmType.NaiveAlgorithm), composelifePreferences.algorithmChoiceState)

        val loadedPreferencesState = composelifePreferences.loadedPreferencesState
        assertTrue(loadedPreferencesState.isSuccess())
        assertEquals(
            AlgorithmType.NaiveAlgorithm,
            loadedPreferencesState.value.algorithmChoice,
        )
    }

    @Test
    fun default_current_shape_type_is_round_rectangle() = runPreferencesTest { composelifePreferences ->
        assertEquals(ResourceState.Loading, composelifePreferences.currentShapeTypeState)

        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(CurrentShapeType.RoundRectangle),
            composelifePreferences.currentShapeTypeState,
        )
    }

    @Test
    fun default_current_shape_is_round_rectangle() = runPreferencesTest { composelifePreferences ->
        assertEquals(ResourceState.Loading, composelifePreferences.currentShapeState)

        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(
                CurrentShape.RoundRectangle(
                    sizeFraction = 1f,
                    cornerFraction = 0f,
                ),
            ),
            composelifePreferences.currentShapeState,
        )
    }

    @Test
    fun default_round_rectangle_session_state_is_correct() = runPreferencesTest { composelifePreferences ->
        assertEquals(ResourceState.Loading, composelifePreferences.roundRectangleSessionState)

        delay(1.milliseconds)

        val roundRectangleSessionState = composelifePreferences.roundRectangleSessionState

        assertIs<ResourceState.Success<SessionValue<CurrentShape.RoundRectangle>>>(roundRectangleSessionState)

        val roundRectangleSessionValue = roundRectangleSessionState.value

        assertNotNull(roundRectangleSessionValue.sessionId)
        assertNotNull(roundRectangleSessionValue.valueId)
        assertEquals(
            CurrentShape.RoundRectangle(
                sizeFraction = 1f,
                cornerFraction = 0f,
            ),
            roundRectangleSessionValue.value,
        )
    }

    @Test
    fun setting_round_rectangle_config_with_null_old_session_id_updates_value() =
        runPreferencesTest { composelifePreferences ->
            assertEquals(ResourceState.Loading, composelifePreferences.currentShapeState)

            delay(1.milliseconds)

            assertEquals(
                ResourceState.Success(
                    CurrentShape.RoundRectangle(
                        sizeFraction = 1f,
                        cornerFraction = 0f,
                    ),
                ),
                composelifePreferences.currentShapeState,
            )

            val newSessionId = UUID.randomUUID()
            val newValueId = UUID.randomUUID()

            composelifePreferences.setRoundRectangleConfig(
                expected = null,
                newValue = SessionValue(
                    newSessionId,
                    newValueId,
                    CurrentShape.RoundRectangle(
                        sizeFraction = 0.8f,
                        cornerFraction = 0.25f,
                    ),
                ),
            )
            delay(1.milliseconds)

            assertEquals(
                ResourceState.Success(
                    CurrentShape.RoundRectangle(
                        sizeFraction = 0.8f,
                        cornerFraction = 0.25f,
                    ),
                ),
                composelifePreferences.currentShapeState,
            )

            val loadedPreferencesState = composelifePreferences.loadedPreferencesState
            assertTrue(loadedPreferencesState.isSuccess())
            assertEquals(
                SessionValue(
                    sessionId = newSessionId,
                    valueId = newValueId,
                    value = CurrentShape.RoundRectangle(
                        sizeFraction = 0.8f,
                        cornerFraction = 0.25f,
                    ),
                ),
                loadedPreferencesState.value.roundRectangleSessionValue,
            )
            assertEquals(
                CurrentShape.RoundRectangle(
                    sizeFraction = 0.8f,
                    cornerFraction = 0.25f,
                ),
                loadedPreferencesState.value.currentShape,
            )
        }

    @Test
    fun default_dark_theme_config_is_follow_system() = runPreferencesTest { composelifePreferences ->
        assertEquals(ResourceState.Loading, composelifePreferences.darkThemeConfigState)

        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(DarkThemeConfig.FollowSystem),
            composelifePreferences.darkThemeConfigState,
        )
    }

    @Test
    fun setting_dark_theme_config_updates_value() = runPreferencesTest { composelifePreferences ->
        assertEquals(ResourceState.Loading, composelifePreferences.darkThemeConfigState)

        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(DarkThemeConfig.FollowSystem),
            composelifePreferences.darkThemeConfigState,
        )

        composelifePreferences.setDarkThemeConfig(DarkThemeConfig.Light)
        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(DarkThemeConfig.Light),
            composelifePreferences.darkThemeConfigState,
        )

        val loadedPreferencesState = composelifePreferences.loadedPreferencesState
        assertTrue(loadedPreferencesState.isSuccess())
        assertEquals(
            DarkThemeConfig.Light,
            loadedPreferencesState.value.darkThemeConfig,
        )
    }

    @Test
    fun default_quick_access_settings_is_empty() = runPreferencesTest { composelifePreferences ->
        assertEquals(ResourceState.Loading, composelifePreferences.quickAccessSettingsState)

        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(emptySet()),
            composelifePreferences.quickAccessSettingsState,
        )
    }

    @Test
    fun adding_quick_access_setting_updates_value() = runPreferencesTest { composelifePreferences ->
        assertEquals(ResourceState.Loading, composelifePreferences.quickAccessSettingsState)

        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(emptySet()),
            composelifePreferences.quickAccessSettingsState,
        )

        composelifePreferences.addQuickAccessSetting(
            QuickAccessSetting.DarkThemeConfig,
        )
        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(setOf(QuickAccessSetting.DarkThemeConfig)),
            composelifePreferences.quickAccessSettingsState,
        )

        val loadedPreferencesState = composelifePreferences.loadedPreferencesState
        assertTrue(loadedPreferencesState.isSuccess())
        assertEquals(
            setOf(QuickAccessSetting.DarkThemeConfig),
            loadedPreferencesState.value.quickAccessSettings,
        )
    }

    @Test
    fun adding_multiple_quick_access_settings_updates_value() = runPreferencesTest { composelifePreferences ->
        assertEquals(ResourceState.Loading, composelifePreferences.quickAccessSettingsState)

        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(emptySet()),
            composelifePreferences.quickAccessSettingsState,
        )

        composelifePreferences.addQuickAccessSetting(
            QuickAccessSetting.DarkThemeConfig,
        )
        composelifePreferences.addQuickAccessSetting(
            QuickAccessSetting.AlgorithmImplementation,
        )
        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(
                setOf(
                    QuickAccessSetting.DarkThemeConfig,
                    QuickAccessSetting.AlgorithmImplementation,
                ),
            ),
            composelifePreferences.quickAccessSettingsState,
        )

        val loadedPreferencesState = composelifePreferences.loadedPreferencesState
        assertTrue(loadedPreferencesState.isSuccess())
        assertEquals(
            setOf(
                QuickAccessSetting.DarkThemeConfig,
                QuickAccessSetting.AlgorithmImplementation,
            ),
            loadedPreferencesState.value.quickAccessSettings,
        )
    }

    @Test
    fun adding_all_quick_access_settings_updates_value() = runPreferencesTest { composelifePreferences ->
        assertEquals(ResourceState.Loading, composelifePreferences.quickAccessSettingsState)

        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(emptySet()),
            composelifePreferences.quickAccessSettingsState,
        )

        composelifePreferences.addQuickAccessSetting(
            QuickAccessSetting.DarkThemeConfig,
        )
        delay(1.milliseconds)
        composelifePreferences.addQuickAccessSetting(
            QuickAccessSetting.AlgorithmImplementation,
        )
        delay(1.milliseconds)
        composelifePreferences.addQuickAccessSetting(
            QuickAccessSetting.CellShapeConfig,
        )
        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(
                setOf(
                    QuickAccessSetting.DarkThemeConfig,
                    QuickAccessSetting.AlgorithmImplementation,
                    QuickAccessSetting.CellShapeConfig,
                ),
            ),
            composelifePreferences.quickAccessSettingsState,
        )

        val loadedPreferencesState = composelifePreferences.loadedPreferencesState
        assertTrue(loadedPreferencesState.isSuccess())
        assertEquals(
            setOf(
                QuickAccessSetting.DarkThemeConfig,
                QuickAccessSetting.AlgorithmImplementation,
                QuickAccessSetting.CellShapeConfig,
            ),
            loadedPreferencesState.value.quickAccessSettings,
        )
    }

    @Test
    fun adding_quick_access_setting_multiple_times_updates_value() = runPreferencesTest { composelifePreferences ->
        assertEquals(ResourceState.Loading, composelifePreferences.quickAccessSettingsState)

        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(emptySet()),
            composelifePreferences.quickAccessSettingsState,
        )

        composelifePreferences.addQuickAccessSetting(
            QuickAccessSetting.DarkThemeConfig,
        )
        delay(1.milliseconds)
        composelifePreferences.addQuickAccessSetting(
            QuickAccessSetting.DarkThemeConfig,
        )
        delay(1.milliseconds)
        composelifePreferences.addQuickAccessSetting(
            QuickAccessSetting.DarkThemeConfig,
        )
        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(setOf(QuickAccessSetting.DarkThemeConfig)),
            composelifePreferences.quickAccessSettingsState,
        )

        val loadedPreferencesState = composelifePreferences.loadedPreferencesState
        assertTrue(loadedPreferencesState.isSuccess())
        assertEquals(
            setOf(QuickAccessSetting.DarkThemeConfig),
            loadedPreferencesState.value.quickAccessSettings,
        )
    }

    @Test
    fun removing_quick_access_setting_multiple_times_updates_value() = runPreferencesTest { composelifePreferences ->
        assertEquals(ResourceState.Loading, composelifePreferences.quickAccessSettingsState)

        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(emptySet()),
            composelifePreferences.quickAccessSettingsState,
        )

        composelifePreferences.addQuickAccessSetting(
            QuickAccessSetting.DarkThemeConfig,
        )
        delay(1.milliseconds)
        composelifePreferences.addQuickAccessSetting(
            QuickAccessSetting.DarkThemeConfig,
        )
        delay(1.milliseconds)
        composelifePreferences.addQuickAccessSetting(
            QuickAccessSetting.DarkThemeConfig,
        )
        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(setOf(QuickAccessSetting.DarkThemeConfig)),
            composelifePreferences.quickAccessSettingsState,
        )

        composelifePreferences.removeQuickAccessSetting(
            QuickAccessSetting.DarkThemeConfig,
        )
        delay(1.milliseconds)
        composelifePreferences.removeQuickAccessSetting(
            QuickAccessSetting.DarkThemeConfig,
        )
        delay(1.milliseconds)
        composelifePreferences.removeQuickAccessSetting(
            QuickAccessSetting.DarkThemeConfig,
        )
        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(emptySet()),
            composelifePreferences.quickAccessSettingsState,
        )

        val loadedPreferencesState = composelifePreferences.loadedPreferencesState
        assertTrue(loadedPreferencesState.isSuccess())
        assertEquals(
            emptySet(),
            loadedPreferencesState.value.quickAccessSettings,
        )
    }

    @Test
    fun adding_and_removing_quick_access_settings_updates_value() = runPreferencesTest { composelifePreferences ->
        assertEquals(ResourceState.Loading, composelifePreferences.quickAccessSettingsState)

        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(emptySet()),
            composelifePreferences.quickAccessSettingsState,
        )

        composelifePreferences.addQuickAccessSetting(
            QuickAccessSetting.DarkThemeConfig,
        )
        delay(1.milliseconds)
        composelifePreferences.addQuickAccessSetting(
            QuickAccessSetting.AlgorithmImplementation,
        )
        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(
                setOf(
                    QuickAccessSetting.DarkThemeConfig,
                    QuickAccessSetting.AlgorithmImplementation,
                ),
            ),
            composelifePreferences.quickAccessSettingsState,
        )

        composelifePreferences.removeQuickAccessSetting(
            QuickAccessSetting.DarkThemeConfig,
        )
        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(setOf(QuickAccessSetting.AlgorithmImplementation)),
            composelifePreferences.quickAccessSettingsState,
        )

        val loadedPreferencesState = composelifePreferences.loadedPreferencesState
        assertTrue(loadedPreferencesState.isSuccess())
        assertEquals(
            setOf(QuickAccessSetting.AlgorithmImplementation),
            loadedPreferencesState.value.quickAccessSettings,
        )
    }

    @Test
    fun default_disabled_agsl_is_disabled() = runPreferencesTest { composelifePreferences ->
        assertEquals(ResourceState.Loading, composelifePreferences.disableAGSLState)

        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(false),
            composelifePreferences.disableAGSLState,
        )
    }

    @Test
    fun setting_disabled_agsl_updates_value() = runPreferencesTest { composelifePreferences ->
        assertEquals(ResourceState.Loading, composelifePreferences.disableAGSLState)

        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(false),
            composelifePreferences.disableAGSLState,
        )

        composelifePreferences.setDisabledAGSL(true)
        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(true),
            composelifePreferences.disableAGSLState,
        )

        val loadedPreferencesState = composelifePreferences.loadedPreferencesState
        assertTrue(loadedPreferencesState.isSuccess())
        assertEquals(
            true,
            loadedPreferencesState.value.disableAGSL,
        )
    }

    @Test
    fun default_disabled_opengl_is_disabled() = runPreferencesTest { composelifePreferences ->
        assertEquals(ResourceState.Loading, composelifePreferences.disableOpenGLState)

        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(false),
            composelifePreferences.disableOpenGLState,
        )
    }

    @Test
    fun setting_disabled_opengl_updates_value() = runPreferencesTest { composelifePreferences ->
        assertEquals(ResourceState.Loading, composelifePreferences.disableOpenGLState)

        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(false),
            composelifePreferences.disableOpenGLState,
        )

        composelifePreferences.setDisableOpenGL(true)
        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(true),
            composelifePreferences.disableOpenGLState,
        )

        val loadedPreferencesState = composelifePreferences.loadedPreferencesState
        assertTrue(loadedPreferencesState.isSuccess())
        assertEquals(
            true,
            loadedPreferencesState.value.disableOpenGL,
        )
    }

    @Test
    fun default_do_not_keep_process_is_false() = runPreferencesTest { composelifePreferences ->
        assertEquals(ResourceState.Loading, composelifePreferences.doNotKeepProcessState)

        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(false),
            composelifePreferences.doNotKeepProcessState,
        )
    }

    @Test
    fun setting_do_not_keep_process_updates_value() = runPreferencesTest { composelifePreferences ->
        assertEquals(ResourceState.Loading, composelifePreferences.doNotKeepProcessState)

        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(false),
            composelifePreferences.doNotKeepProcessState,
        )

        composelifePreferences.setDoNotKeepProcess(true)
        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(true),
            composelifePreferences.doNotKeepProcessState,
        )

        val loadedPreferencesState = composelifePreferences.loadedPreferencesState
        assertTrue(loadedPreferencesState.isSuccess())
        assertEquals(
            true,
            loadedPreferencesState.value.doNotKeepProcess,
        )
    }

    @Test
    fun default_touch_tool_config_is_pan() = runPreferencesTest { composelifePreferences ->
        assertEquals(ResourceState.Loading, composelifePreferences.touchToolConfigState)

        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(ToolConfig.Pan),
            composelifePreferences.touchToolConfigState,
        )
    }

    @Test
    fun setting_touch_tool_config_updates_value() = runPreferencesTest { composelifePreferences ->
        assertEquals(ResourceState.Loading, composelifePreferences.doNotKeepProcessState)

        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(ToolConfig.Pan),
            composelifePreferences.touchToolConfigState,
        )

        composelifePreferences.setTouchToolConfig(ToolConfig.Draw)
        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(ToolConfig.Draw),
            composelifePreferences.touchToolConfigState,
        )

        val loadedPreferencesState = composelifePreferences.loadedPreferencesState
        assertTrue(loadedPreferencesState.isSuccess())
        assertEquals(
            ToolConfig.Draw,
            loadedPreferencesState.value.touchToolConfig,
        )
    }

    @Test
    fun default_stylus_tool_config_is_draw() = runPreferencesTest { composelifePreferences ->
        assertEquals(ResourceState.Loading, composelifePreferences.stylusToolConfigState)

        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(ToolConfig.Draw),
            composelifePreferences.stylusToolConfigState,
        )
    }

    @Test
    fun setting_stylus_tool_config_updates_value() = runPreferencesTest { composelifePreferences ->
        assertEquals(ResourceState.Loading, composelifePreferences.doNotKeepProcessState)

        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(ToolConfig.Draw),
            composelifePreferences.stylusToolConfigState,
        )

        composelifePreferences.setStylusToolConfig(ToolConfig.Erase)
        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(ToolConfig.Erase),
            composelifePreferences.stylusToolConfigState,
        )

        val loadedPreferencesState = composelifePreferences.loadedPreferencesState
        assertTrue(loadedPreferencesState.isSuccess())
        assertEquals(
            ToolConfig.Erase,
            loadedPreferencesState.value.stylusToolConfig,
        )
    }

    @Test
    fun default_mouse_tool_config_is_draw() = runPreferencesTest { composelifePreferences ->
        assertEquals(ResourceState.Loading, composelifePreferences.mouseToolConfigState)

        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(ToolConfig.Draw),
            composelifePreferences.mouseToolConfigState,
        )
    }

    @Test
    fun setting_mouse_tool_config_updates_value() = runPreferencesTest { composelifePreferences ->
        assertEquals(ResourceState.Loading, composelifePreferences.doNotKeepProcessState)

        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(ToolConfig.Draw),
            composelifePreferences.mouseToolConfigState,
        )

        composelifePreferences.setMouseToolConfig(ToolConfig.Erase)
        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(ToolConfig.Erase),
            composelifePreferences.mouseToolConfigState,
        )

        val loadedPreferencesState = composelifePreferences.loadedPreferencesState
        assertTrue(loadedPreferencesState.isSuccess())
        assertEquals(
            ToolConfig.Erase,
            loadedPreferencesState.value.mouseToolConfig,
        )
    }

    @Test
    fun default_completed_clipboard_watching_onboarding_is_false() = runPreferencesTest { composelifePreferences ->
        assertEquals(ResourceState.Loading, composelifePreferences.completedClipboardWatchingOnboardingState)

        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(false),
            composelifePreferences.completedClipboardWatchingOnboardingState,
        )
    }

    @Test
    fun setting_completed_clipboard_watching_onboarding_updates_value() = runPreferencesTest { composelifePreferences ->
        assertEquals(ResourceState.Loading, composelifePreferences.completedClipboardWatchingOnboardingState)

        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(false),
            composelifePreferences.completedClipboardWatchingOnboardingState,
        )

        composelifePreferences.setCompletedClipboardWatchingOnboarding(true)
        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(true),
            composelifePreferences.completedClipboardWatchingOnboardingState,
        )

        val loadedPreferencesState = composelifePreferences.loadedPreferencesState
        assertTrue(loadedPreferencesState.isSuccess())
        assertTrue(
            loadedPreferencesState.value.completedClipboardWatchingOnboarding,
        )
    }

    @Test
    fun default_enable_clipboard_watching_is_false() = runPreferencesTest { composelifePreferences ->
        assertEquals(ResourceState.Loading, composelifePreferences.enableClipboardWatchingState)

        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(false),
            composelifePreferences.enableClipboardWatchingState,
        )
    }

    @Test
    fun setting_enable_clipboard_watching_updates_value() = runPreferencesTest { composelifePreferences ->
        assertEquals(ResourceState.Loading, composelifePreferences.enableClipboardWatchingState)

        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(false),
            composelifePreferences.enableClipboardWatchingState,
        )

        composelifePreferences.setEnableClipboardWatching(true)
        delay(1.milliseconds)

        assertEquals(
            ResourceState.Success(true),
            composelifePreferences.enableClipboardWatchingState,
        )

        val loadedPreferencesState = composelifePreferences.loadedPreferencesState
        assertTrue(loadedPreferencesState.isSuccess())
        assertTrue(
            loadedPreferencesState.value.enableClipboardWatching,
        )
    }
}
