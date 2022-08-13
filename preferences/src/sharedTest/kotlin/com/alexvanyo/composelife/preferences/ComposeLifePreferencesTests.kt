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

import androidx.test.ext.junit.runners.AndroidJUnit4
import com.alexvanyo.composelife.dispatchers.di.TestDispatcherModule
import com.alexvanyo.composelife.resourcestate.ResourceState
import dagger.hilt.android.testing.BindValue
import dagger.hilt.android.testing.HiltAndroidRule
import dagger.hilt.android.testing.HiltAndroidTest
import dagger.hilt.android.testing.UninstallModules
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.launch
import kotlinx.coroutines.test.StandardTestDispatcher
import kotlinx.coroutines.test.resetMain
import kotlinx.coroutines.test.runCurrent
import kotlinx.coroutines.test.runTest
import kotlinx.coroutines.test.setMain
import org.junit.After
import org.junit.Before
import org.junit.Rule
import org.junit.Test
import org.junit.runner.RunWith
import javax.inject.Inject
import kotlin.test.assertEquals

@OptIn(ExperimentalCoroutinesApi::class)
@HiltAndroidTest
@UninstallModules(TestDispatcherModule::class)
@RunWith(AndroidJUnit4::class)
class ComposeLifePreferencesTests {

    @get:Rule
    val preferencesRule = PreferencesRule()

    @get:Rule
    val hiltAndroidRule = HiltAndroidRule(this)

    @BindValue
    val fileProvider = preferencesRule.fileProvider

    @Inject
    lateinit var composeLifePreferences: DefaultComposeLifePreferences

    @BindValue
    val testDispatcher = StandardTestDispatcher().also(Dispatchers::setMain)

    @Before
    fun setup() {
        hiltAndroidRule.inject()
    }

    @After
    fun teardown() {
        Dispatchers.resetMain()
    }

    @Test
    fun default_algorithm_choice_is_hashlife() = runTest {
        backgroundScope.launch {
            composeLifePreferences.update()
        }

        assertEquals(ResourceState.Loading, composeLifePreferences.algorithmChoiceState)

        runCurrent()

        assertEquals(
            ResourceState.Success(AlgorithmType.HashLifeAlgorithm),
            composeLifePreferences.algorithmChoiceState,
        )
    }

    @Test
    fun setting_algorithm_choice_updates_value() = runTest {
        backgroundScope.launch {
            composeLifePreferences.update()
        }

        assertEquals(ResourceState.Loading, composeLifePreferences.algorithmChoiceState)

        runCurrent()

        assertEquals(
            ResourceState.Success(AlgorithmType.HashLifeAlgorithm),
            composeLifePreferences.algorithmChoiceState,
        )

        composeLifePreferences.setAlgorithmChoice(AlgorithmType.NaiveAlgorithm)
        runCurrent()

        assertEquals(ResourceState.Success(AlgorithmType.NaiveAlgorithm), composeLifePreferences.algorithmChoiceState)
    }

    @Test
    fun default_current_shape_is_round_rectangle() = runTest {
        backgroundScope.launch {
            composeLifePreferences.update()
        }

        assertEquals(ResourceState.Loading, composeLifePreferences.currentShapeState)

        runCurrent()

        assertEquals(
            ResourceState.Success(
                CurrentShape.RoundRectangle(
                    sizeFraction = 1f,
                    cornerFraction = 0f,
                ),
            ),
            composeLifePreferences.currentShapeState,
        )
    }

    @Test
    fun setting_round_rectangle_config_updates_value() = runTest {
        backgroundScope.launch {
            composeLifePreferences.update()
        }

        assertEquals(ResourceState.Loading, composeLifePreferences.currentShapeState)

        runCurrent()

        assertEquals(
            ResourceState.Success(
                CurrentShape.RoundRectangle(
                    sizeFraction = 1f,
                    cornerFraction = 0f,
                ),
            ),
            composeLifePreferences.currentShapeState,
        )

        composeLifePreferences.setRoundRectangleConfig { roundRectangle ->
            roundRectangle.copy(
                sizeFraction = 0.8f,
                cornerFraction = 0.25f,
            )
        }
        runCurrent()

        assertEquals(
            ResourceState.Success(
                CurrentShape.RoundRectangle(
                    sizeFraction = 0.8f,
                    cornerFraction = 0.25f,
                ),
            ),
            composeLifePreferences.currentShapeState,
        )
    }

    @Test
    fun default_dark_theme_config_is_follow_system() = runTest {
        backgroundScope.launch {
            composeLifePreferences.update()
        }

        assertEquals(ResourceState.Loading, composeLifePreferences.darkThemeConfigState)

        runCurrent()

        assertEquals(
            ResourceState.Success(DarkThemeConfig.FollowSystem),
            composeLifePreferences.darkThemeConfigState,
        )
    }

    @Test
    fun setting_dark_theme_config_updates_value() = runTest {
        backgroundScope.launch {
            composeLifePreferences.update()
        }

        assertEquals(ResourceState.Loading, composeLifePreferences.darkThemeConfigState)

        runCurrent()

        assertEquals(
            ResourceState.Success(DarkThemeConfig.FollowSystem),
            composeLifePreferences.darkThemeConfigState,
        )

        composeLifePreferences.setDarkThemeConfig(DarkThemeConfig.Light)
        runCurrent()

        assertEquals(
            ResourceState.Success(DarkThemeConfig.Light),
            composeLifePreferences.darkThemeConfigState,
        )
    }

    @Test
    fun default_quick_access_settings_is_empty() = runTest {
        backgroundScope.launch {
            composeLifePreferences.update()
        }

        assertEquals(ResourceState.Loading, composeLifePreferences.quickAccessSettings)

        runCurrent()

        assertEquals(
            ResourceState.Success(emptySet()),
            composeLifePreferences.quickAccessSettings,
        )
    }

    @Test
    fun adding_quick_access_setting_updates_value() = runTest {
        backgroundScope.launch {
            composeLifePreferences.update()
        }

        assertEquals(ResourceState.Loading, composeLifePreferences.quickAccessSettings)

        runCurrent()

        assertEquals(
            ResourceState.Success(emptySet()),
            composeLifePreferences.quickAccessSettings,
        )

        composeLifePreferences.addQuickAccessSetting(
            QuickAccessSetting.DarkThemeConfig,
        )
        runCurrent()

        assertEquals(
            ResourceState.Success(setOf(QuickAccessSetting.DarkThemeConfig)),
            composeLifePreferences.quickAccessSettings,
        )
    }

    @Test
    fun adding_multiple_quick_access_settings_updates_value() = runTest {
        backgroundScope.launch {
            composeLifePreferences.update()
        }

        assertEquals(ResourceState.Loading, composeLifePreferences.quickAccessSettings)

        runCurrent()

        assertEquals(
            ResourceState.Success(emptySet()),
            composeLifePreferences.quickAccessSettings,
        )

        composeLifePreferences.addQuickAccessSetting(
            QuickAccessSetting.DarkThemeConfig,
        )
        composeLifePreferences.addQuickAccessSetting(
            QuickAccessSetting.AlgorithmImplementation,
        )
        runCurrent()

        assertEquals(
            ResourceState.Success(
                setOf(
                    QuickAccessSetting.DarkThemeConfig,
                    QuickAccessSetting.AlgorithmImplementation,
                ),
            ),
            composeLifePreferences.quickAccessSettings,
        )
    }

    @Test
    fun adding_all_quick_access_settings_updates_value() = runTest {
        backgroundScope.launch {
            composeLifePreferences.update()
        }

        assertEquals(ResourceState.Loading, composeLifePreferences.quickAccessSettings)

        runCurrent()

        assertEquals(
            ResourceState.Success(emptySet()),
            composeLifePreferences.quickAccessSettings,
        )

        composeLifePreferences.addQuickAccessSetting(
            QuickAccessSetting.DarkThemeConfig,
        )
        runCurrent()
        composeLifePreferences.addQuickAccessSetting(
            QuickAccessSetting.AlgorithmImplementation,
        )
        runCurrent()
        composeLifePreferences.addQuickAccessSetting(
            QuickAccessSetting.CellShapeConfig,
        )
        runCurrent()

        assertEquals(
            ResourceState.Success(
                setOf(
                    QuickAccessSetting.DarkThemeConfig,
                    QuickAccessSetting.AlgorithmImplementation,
                    QuickAccessSetting.CellShapeConfig,
                ),
            ),
            composeLifePreferences.quickAccessSettings,
        )
    }

    @Test
    fun adding_quick_access_setting_multiple_times_updates_value() = runTest {
        backgroundScope.launch {
            composeLifePreferences.update()
        }

        assertEquals(ResourceState.Loading, composeLifePreferences.quickAccessSettings)

        runCurrent()

        assertEquals(
            ResourceState.Success(emptySet()),
            composeLifePreferences.quickAccessSettings,
        )

        composeLifePreferences.addQuickAccessSetting(
            QuickAccessSetting.DarkThemeConfig,
        )
        runCurrent()
        composeLifePreferences.addQuickAccessSetting(
            QuickAccessSetting.DarkThemeConfig,
        )
        runCurrent()
        composeLifePreferences.addQuickAccessSetting(
            QuickAccessSetting.DarkThemeConfig,
        )
        runCurrent()

        assertEquals(
            ResourceState.Success(setOf(QuickAccessSetting.DarkThemeConfig)),
            composeLifePreferences.quickAccessSettings,
        )
    }

    @Test
    fun removing_quick_access_setting_multiple_times_updates_value() = runTest {
        backgroundScope.launch {
            composeLifePreferences.update()
        }

        assertEquals(ResourceState.Loading, composeLifePreferences.quickAccessSettings)

        runCurrent()

        assertEquals(
            ResourceState.Success(emptySet()),
            composeLifePreferences.quickAccessSettings,
        )

        composeLifePreferences.addQuickAccessSetting(
            QuickAccessSetting.DarkThemeConfig,
        )
        runCurrent()
        composeLifePreferences.addQuickAccessSetting(
            QuickAccessSetting.DarkThemeConfig,
        )
        runCurrent()
        composeLifePreferences.addQuickAccessSetting(
            QuickAccessSetting.DarkThemeConfig,
        )
        runCurrent()

        assertEquals(
            ResourceState.Success(setOf(QuickAccessSetting.DarkThemeConfig)),
            composeLifePreferences.quickAccessSettings,
        )

        composeLifePreferences.removeQuickAccessSetting(
            QuickAccessSetting.DarkThemeConfig,
        )
        runCurrent()
        composeLifePreferences.removeQuickAccessSetting(
            QuickAccessSetting.DarkThemeConfig,
        )
        runCurrent()
        composeLifePreferences.removeQuickAccessSetting(
            QuickAccessSetting.DarkThemeConfig,
        )
        runCurrent()

        assertEquals(
            ResourceState.Success(emptySet()),
            composeLifePreferences.quickAccessSettings,
        )
    }

    @Test
    fun adding_and_removing_quick_access_settings_updates_value() = runTest {
        backgroundScope.launch {
            composeLifePreferences.update()
        }

        assertEquals(ResourceState.Loading, composeLifePreferences.quickAccessSettings)

        runCurrent()

        assertEquals(
            ResourceState.Success(emptySet()),
            composeLifePreferences.quickAccessSettings,
        )

        composeLifePreferences.addQuickAccessSetting(
            QuickAccessSetting.DarkThemeConfig,
        )
        runCurrent()
        composeLifePreferences.addQuickAccessSetting(
            QuickAccessSetting.AlgorithmImplementation,
        )
        runCurrent()

        assertEquals(
            ResourceState.Success(
                setOf(
                    QuickAccessSetting.DarkThemeConfig,
                    QuickAccessSetting.AlgorithmImplementation,
                ),
            ),
            composeLifePreferences.quickAccessSettings,
        )

        composeLifePreferences.removeQuickAccessSetting(
            QuickAccessSetting.DarkThemeConfig,
        )
        runCurrent()

        assertEquals(
            ResourceState.Success(setOf(QuickAccessSetting.AlgorithmImplementation)),
            composeLifePreferences.quickAccessSettings,
        )
    }

    @Test
    fun default_disabled_agsl_is_disabled() = runTest {
        backgroundScope.launch {
            composeLifePreferences.update()
        }

        assertEquals(ResourceState.Loading, composeLifePreferences.disableAGSLState)

        runCurrent()

        assertEquals(
            ResourceState.Success(false),
            composeLifePreferences.disableAGSLState,
        )
    }

    @Test
    fun setting_disabled_agsl_updates_value() = runTest {
        backgroundScope.launch {
            composeLifePreferences.update()
        }

        assertEquals(ResourceState.Loading, composeLifePreferences.disableAGSLState)

        runCurrent()

        assertEquals(
            ResourceState.Success(false),
            composeLifePreferences.disableAGSLState,
        )

        composeLifePreferences.setDisabledAGSL(true)
        runCurrent()

        assertEquals(
            ResourceState.Success(true),
            composeLifePreferences.disableAGSLState,
        )
    }

    @Test
    fun default_disabled_opengl_is_disabled() = runTest {
        backgroundScope.launch {
            composeLifePreferences.update()
        }

        assertEquals(ResourceState.Loading, composeLifePreferences.disableOpenGLState)

        runCurrent()

        assertEquals(
            ResourceState.Success(false),
            composeLifePreferences.disableOpenGLState,
        )
    }

    @Test
    fun setting_disabled_opengl_updates_value() = runTest {
        backgroundScope.launch {
            composeLifePreferences.update()
        }

        assertEquals(ResourceState.Loading, composeLifePreferences.disableOpenGLState)

        runCurrent()

        assertEquals(
            ResourceState.Success(false),
            composeLifePreferences.disableOpenGLState,
        )

        composeLifePreferences.setDisableOpenGL(true)
        runCurrent()

        assertEquals(
            ResourceState.Success(true),
            composeLifePreferences.disableOpenGLState,
        )
    }
}
