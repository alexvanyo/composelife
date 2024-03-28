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

import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.compose.runtime.snapshots.Snapshot
import com.alexvanyo.composelife.preferences.CurrentShape.RoundRectangle
import com.alexvanyo.composelife.preferences.proto.AlgorithmProto
import com.alexvanyo.composelife.preferences.proto.CurrentShapeTypeProto
import com.alexvanyo.composelife.preferences.proto.DarkThemeConfigProto
import com.alexvanyo.composelife.preferences.proto.PreferencesProto
import com.alexvanyo.composelife.preferences.proto.QuickAccessSettingProto
import com.alexvanyo.composelife.preferences.proto.ToolConfigProto
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.resourcestate.asResourceState
import com.alexvanyo.composelife.scopes.Singleton
import com.alexvanyo.composelife.sessionvalue.SessionValue
import com.alexvanyo.composelife.updatable.Updatable
import kotlinx.coroutines.flow.collect
import kotlinx.coroutines.flow.map
import kotlinx.coroutines.flow.onEach
import kotlinx.coroutines.flow.retry
import me.tatarka.inject.annotations.Inject

@Singleton
@Inject
class DefaultComposeLifePreferences(
    private val dataStore: PreferencesDataStore,
) : ComposeLifePreferences, Updatable {

    override var loadedPreferencesState:
        ResourceState<LoadedComposeLifePreferences> by mutableStateOf(ResourceState.Loading)
        private set

    override suspend fun update(): Nothing {
        dataStore.data
            .retry()
            .map(PreferencesProto::toLoadedComposeLifePreferences)
            .asResourceState()
            .onEach {
                Snapshot.withMutableSnapshot {
                    loadedPreferencesState = it
                }
            }
            .collect()

        error("data can not complete normally")
    }

    override suspend fun update(
        block: ComposeLifePreferencesTransform.() -> Unit,
    ) {
        dataStore.updateData { preferencesProto ->
            PreferencesProtoTransform(preferencesProto).apply(block).newPreferencesProto
        }
    }
}

@Suppress("TooManyFunctions")
private class PreferencesProtoTransform(
    previousPreferencesProto: PreferencesProto,
) : ComposeLifePreferencesTransform {
    var newPreferencesProto: PreferencesProto = previousPreferencesProto

    override val previousLoadedComposeLifePreferences: LoadedComposeLifePreferences =
        previousPreferencesProto.toLoadedComposeLifePreferences()

    override fun setAlgorithmChoice(algorithm: AlgorithmType) {
        newPreferencesProto = newPreferencesProto.copy(
            algorithm = when (algorithm) {
                AlgorithmType.HashLifeAlgorithm -> AlgorithmProto.HASHLIFE
                AlgorithmType.NaiveAlgorithm -> AlgorithmProto.NAIVE
            },
        )
    }

    override fun setCurrentShapeType(currentShapeType: CurrentShapeType) {
        newPreferencesProto = newPreferencesProto.copy(
            current_shape_type = when (currentShapeType) {
                CurrentShapeType.RoundRectangle -> CurrentShapeTypeProto.ROUND_RECTANGLE
            },
        )
    }

    override fun setDarkThemeConfig(darkThemeConfig: DarkThemeConfig) {
        newPreferencesProto = newPreferencesProto.copy(
            dark_theme_config = when (darkThemeConfig) {
                DarkThemeConfig.FollowSystem -> DarkThemeConfigProto.SYSTEM
                DarkThemeConfig.Dark -> DarkThemeConfigProto.DARK
                DarkThemeConfig.Light -> DarkThemeConfigProto.LIGHT
            },
        )
    }

    override fun setRoundRectangleConfig(
        expected: SessionValue<RoundRectangle>?,
        newValue: SessionValue<RoundRectangle>,
    ) {
        val oldValue = newPreferencesProto.roundRectangleSessionValue
        if (expected == null || expected == oldValue) {
            newPreferencesProto = newPreferencesProto.copy(
                round_rectangle = newValue.value.toProto(),
                round_rectangle_session_id = newValue.sessionId.toProto(),
                round_rectangle_value_id = newValue.valueId.toProto(),
            )
        }
    }

    override fun addQuickAccessSetting(quickAccessSetting: QuickAccessSetting) =
        updateQuickAccessSetting(true, quickAccessSetting)

    override fun removeQuickAccessSetting(quickAccessSetting: QuickAccessSetting) =
        updateQuickAccessSetting(false, quickAccessSetting)

    private fun updateQuickAccessSetting(include: Boolean, quickAccessSetting: QuickAccessSetting) {
        val quickAccessSettingProto = when (quickAccessSetting) {
            QuickAccessSetting.AlgorithmImplementation -> QuickAccessSettingProto.ALGORITHM_IMPLEMENTATION
            QuickAccessSetting.CellShapeConfig -> QuickAccessSettingProto.CELL_SHAPE_CONFIG
            QuickAccessSetting.DarkThemeConfig -> QuickAccessSettingProto.DARK_THEME_CONFIG
            QuickAccessSetting.DisableAGSL -> QuickAccessSettingProto.DISABLE_AGSL
            QuickAccessSetting.DisableOpenGL -> QuickAccessSettingProto.DISABLE_OPENGL
            QuickAccessSetting.DoNotKeepProcess -> QuickAccessSettingProto.DO_NOT_KEEP_PROCESS
            QuickAccessSetting.EnableClipboardWatching -> QuickAccessSettingProto.ENABLE_CLIPBOARD_WATCHING
        }

        val oldQuickAccessSettings = newPreferencesProto.quick_access_settings.toSet()
        val newQuickAccessSetting = if (include) {
            oldQuickAccessSettings + quickAccessSettingProto
        } else {
            oldQuickAccessSettings - quickAccessSettingProto
        }

        newPreferencesProto = newPreferencesProto.copy(
            quick_access_settings = newQuickAccessSetting.toList(),
        )
    }

    override fun setDisabledAGSL(disabled: Boolean) {
        newPreferencesProto = newPreferencesProto.copy(
            disable_agsl = disabled,
        )
    }

    override fun setDisableOpenGL(disabled: Boolean) {
        newPreferencesProto = newPreferencesProto.copy(
            disable_opengl = disabled,
        )
    }

    override fun setDoNotKeepProcess(doNotKeepProcess: Boolean) {
        newPreferencesProto = newPreferencesProto.copy(
            do_not_keep_process = doNotKeepProcess,
        )
    }

    override fun setTouchToolConfig(toolConfig: ToolConfig) {
        newPreferencesProto = newPreferencesProto.copy(
            touch_tool_config = toolConfig.toProto(),
        )
    }

    override fun setStylusToolConfig(toolConfig: ToolConfig) {
        newPreferencesProto = newPreferencesProto.copy(
            stylus_tool_config = toolConfig.toProto(),
        )
    }

    override fun setMouseToolConfig(toolConfig: ToolConfig) {
        newPreferencesProto = newPreferencesProto.copy(
            mouse_tool_config = toolConfig.toProto(),
        )
    }

    override fun setCompletedClipboardWatchingOnboarding(completed: Boolean) {
        newPreferencesProto = newPreferencesProto.copy(
            completed_clipboard_watching_onboarding = completed,
        )
    }

    override fun setEnableClipboardWatching(enabled: Boolean) {
        newPreferencesProto = newPreferencesProto.copy(
            enable_clipboard_watching = enabled,
        )
    }
}

@Suppress("LongMethod", "ComplexMethod")
private fun PreferencesProto.toLoadedComposeLifePreferences(): LoadedComposeLifePreferences {
    val quickAccessSettings =
        quick_access_settings.mapNotNull { quickAccessSettingProto ->
            when (quickAccessSettingProto) {
                QuickAccessSettingProto.ALGORITHM_IMPLEMENTATION ->
                    QuickAccessSetting.AlgorithmImplementation
                QuickAccessSettingProto.DARK_THEME_CONFIG ->
                    QuickAccessSetting.DarkThemeConfig
                QuickAccessSettingProto.CELL_SHAPE_CONFIG ->
                    QuickAccessSetting.CellShapeConfig
                QuickAccessSettingProto.DISABLE_AGSL ->
                    QuickAccessSetting.DisableAGSL
                QuickAccessSettingProto.DISABLE_OPENGL ->
                    QuickAccessSetting.DisableOpenGL
                QuickAccessSettingProto.DO_NOT_KEEP_PROCESS ->
                    QuickAccessSetting.DoNotKeepProcess
                QuickAccessSettingProto.ENABLE_CLIPBOARD_WATCHING ->
                    QuickAccessSetting.EnableClipboardWatching
                QuickAccessSettingProto.SETTINGS_UNKNOWN,
                -> null
            }
        }.toSet()

    val algorithmChoice =
        when (algorithm) {
            AlgorithmProto.ALGORITHM_UNKNOWN,
            AlgorithmProto.DEFAULT,
            AlgorithmProto.HASHLIFE,
            -> AlgorithmType.HashLifeAlgorithm
            AlgorithmProto.NAIVE -> AlgorithmType.NaiveAlgorithm
        }

    val currentShapeType =
        when (current_shape_type) {
            CurrentShapeTypeProto.CURRENT_SHAPE_TYPE_UNKNOWN,
            CurrentShapeTypeProto.ROUND_RECTANGLE,
            -> CurrentShapeType.RoundRectangle
        }

    val darkThemeConfig =
        when (dark_theme_config) {
            DarkThemeConfigProto.DARK_THEME_UNKNOWN,
            DarkThemeConfigProto.SYSTEM,
            -> DarkThemeConfig.FollowSystem
            DarkThemeConfigProto.DARK -> DarkThemeConfig.Dark
            DarkThemeConfigProto.LIGHT -> DarkThemeConfig.Light
        }
    val disableAGSL = disable_agsl
    val disableOpenGL = disable_opengl
    val doNotKeepProcess = do_not_keep_process
    val touchToolConfig =
        when (touch_tool_config) {
            ToolConfigProto.TOOL_CONFIG_UNKNOWN,
            ToolConfigProto.PAN,
            -> ToolConfig.Pan
            ToolConfigProto.DRAW -> ToolConfig.Draw
            ToolConfigProto.ERASE -> ToolConfig.Erase
            ToolConfigProto.SELECT -> ToolConfig.Select
            ToolConfigProto.NONE -> ToolConfig.None
        }
    val stylusToolConfig =
        when (stylus_tool_config) {
            ToolConfigProto.PAN -> ToolConfig.Pan
            ToolConfigProto.TOOL_CONFIG_UNKNOWN,
            ToolConfigProto.DRAW,
            -> ToolConfig.Draw
            ToolConfigProto.ERASE -> ToolConfig.Erase
            ToolConfigProto.SELECT -> ToolConfig.Select
            ToolConfigProto.NONE -> ToolConfig.None
        }
    val mouseToolConfig =
        when (mouse_tool_config) {
            ToolConfigProto.PAN -> ToolConfig.Pan
            ToolConfigProto.TOOL_CONFIG_UNKNOWN,
            ToolConfigProto.DRAW,
            -> ToolConfig.Draw
            ToolConfigProto.ERASE -> ToolConfig.Erase
            ToolConfigProto.SELECT -> ToolConfig.Select
            ToolConfigProto.NONE -> ToolConfig.None
        }
    val completedClipboardWatchingOnboarding = completed_clipboard_watching_onboarding
    val enableClipboardWatching = enable_clipboard_watching

    return LoadedComposeLifePreferences(
        quickAccessSettings = quickAccessSettings,
        algorithmChoice = algorithmChoice,
        currentShapeType = currentShapeType,
        roundRectangleSessionValue = roundRectangleSessionValue,
        darkThemeConfig = darkThemeConfig,
        disableAGSL = disableAGSL,
        disableOpenGL = disableOpenGL,
        doNotKeepProcess = doNotKeepProcess,
        touchToolConfig = touchToolConfig,
        stylusToolConfig = stylusToolConfig,
        mouseToolConfig = mouseToolConfig,
        completedClipboardWatchingOnboarding = completedClipboardWatchingOnboarding,
        enableClipboardWatching = enableClipboardWatching,
    )
}

private val PreferencesProto.roundRectangleSessionValue: SessionValue<RoundRectangle> get() {
    val roundRectangleConfig = round_rectangle.toResolved()
    val roundRectangleSessionId = checkNotNull(round_rectangle_session_id.toResolved()) {
        "Round rectangle session id was null!"
    }
    val roundRectangleValueId = checkNotNull(round_rectangle_value_id.toResolved()) {
        "Round rectangle value id was null!"
    }
    return SessionValue(
        sessionId = roundRectangleSessionId,
        valueId = roundRectangleValueId,
        value = roundRectangleConfig,
    )
}
