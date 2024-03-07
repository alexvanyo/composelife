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
@file:Suppress("MatchingDeclarationName")

package com.alexvanyo.composelife.ui.app.action.settings

import androidx.compose.foundation.layout.Column
import androidx.compose.runtime.Composable
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.ui.Modifier
import androidx.compose.ui.platform.testTag
import com.alexvanyo.composelife.preferences.QuickAccessSetting
import com.alexvanyo.composelife.preferences.addQuickAccessSetting
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.di.LoadedComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.removeQuickAccessSetting
import kotlinx.coroutines.launch

interface SettingUiInjectEntryPoint :
    AlgorithmImplementationUiInjectEntryPoint,
    CellShapeConfigUiInjectEntryPoint,
    ComposeLifePreferencesProvider,
    DarkThemeConfigUiInjectEntryPoint,
    DisableAGSLUiInjectEntryPoint,
    DisableOpenGLUiInjectEntryPoint,
    DoNotKeepProcessUiInjectEntryPoint,
    EnableClipboardWatchingUiInjectEntryPoint

interface SettingUiLocalEntryPoint :
    AlgorithmImplementationUiLocalEntryPoint,
    CellShapeConfigUiLocalEntryPoint,
    CellStatePreviewUiLocalEntryPoint,
    DarkThemeConfigUiLocalEntryPoint,
    DisableAGSLUiLocalEntryPoint,
    DisableOpenGLUiLocalEntryPoint,
    DoNotKeepProcessUiLocalEntryPoint,
    EnableClipboardWatchingUiLocalEntryPoint,
    LoadedComposeLifePreferencesProvider

/**
 * Displays the setting UI for the given [setting].
 *
 * If [onOpenInSettingsClicked] is not null, then a button will be displayed to open the given
 * setting that will invoke [onOpenInSettingsClicked].
 */
context(SettingUiInjectEntryPoint, SettingUiLocalEntryPoint)
@Composable
fun SettingUi(
    setting: Setting,
    modifier: Modifier = Modifier,
    onOpenInSettingsClicked: ((Setting) -> Unit)? = null,
) {
    Column(
        modifier = modifier.testTag("SettingUi:${setting.name}"),
    ) {
        val quickAccessSetting = setting.quickAccessSetting
        if (quickAccessSetting != null) {
            val coroutineScope = rememberCoroutineScope()
            QuickAccessSettingHeader(
                isFavorite = quickAccessSetting in preferences.quickAccessSettings,
                setIsFavorite = { isFavorite ->
                    coroutineScope.launch {
                        if (isFavorite) {
                            composeLifePreferences.addQuickAccessSetting(quickAccessSetting)
                        } else {
                            composeLifePreferences.removeQuickAccessSetting(quickAccessSetting)
                        }
                    }
                },
                onOpenInSettingsClicked = onOpenInSettingsClicked?.let { { it(setting) } },
            )
        }

        when (setting) {
            Setting.AlgorithmImplementation -> AlgorithmImplementationUi()
            Setting.CellStatePreview -> CellStatePreviewUi()
            Setting.DarkThemeConfig -> DarkThemeConfigUi()
            Setting.CellShapeConfig -> CellShapeConfigUi()
            Setting.DisableAGSL -> DisableAGSLUi()
            Setting.DisableOpenGL -> DisableOpenGLUi()
            Setting.DoNotKeepProcess -> DoNotKeepProcessUi()
            Setting.EnableClipboardWatching -> EnableClipboardWatchingUi()
        }
    }
}

/**
 * Displays the setting UI for the given [quickAccessSetting].
 */
context(SettingUiInjectEntryPoint, SettingUiLocalEntryPoint)
@Composable
fun SettingUi(
    quickAccessSetting: QuickAccessSetting,
    onOpenInSettingsClicked: (Setting) -> Unit,
    modifier: Modifier = Modifier,
) {
    SettingUi(
        setting = when (quickAccessSetting) {
            QuickAccessSetting.AlgorithmImplementation -> Setting.AlgorithmImplementation
            QuickAccessSetting.CellShapeConfig -> Setting.CellShapeConfig
            QuickAccessSetting.DarkThemeConfig -> Setting.DarkThemeConfig
            QuickAccessSetting.DisableAGSL -> Setting.DisableAGSL
            QuickAccessSetting.DisableOpenGL -> Setting.DisableOpenGL
            QuickAccessSetting.DoNotKeepProcess -> Setting.DoNotKeepProcess
            QuickAccessSetting.EnableClipboardWatching -> Setting.EnableClipboardWatching
        },
        modifier = modifier,
        onOpenInSettingsClicked = onOpenInSettingsClicked,
    )
}
