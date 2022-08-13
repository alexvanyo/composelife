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

package com.alexvanyo.composelife.ui.action.settings

import androidx.compose.foundation.layout.Column
import androidx.compose.runtime.Composable
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.ui.Modifier
import androidx.compose.ui.platform.testTag
import com.alexvanyo.composelife.preferences.QuickAccessSetting
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.resourcestate.ResourceState
import dagger.hilt.EntryPoint
import dagger.hilt.InstallIn
import dagger.hilt.android.components.ActivityComponent
import kotlinx.coroutines.launch

@EntryPoint
@InstallIn(ActivityComponent::class)
interface SettingUiEntryPoint :
    AlgorithmImplementationUiEntryPoint,
    CellShapeConfigUiEntryPoint,
    CellStatePreviewUiEntryPoint,
    ComposeLifePreferencesProvider,
    DarkThemeConfigUiEntryPoint,
    DisableAGSLUiEntryPoint,
    DisableOpenGLUiEntryPoint

context(SettingUiEntryPoint)
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
            when (val quickAccessSettings = composeLifePreferences.quickAccessSettings) {
                ResourceState.Loading, is ResourceState.Failure -> Unit
                is ResourceState.Success -> {
                    val coroutineScope = rememberCoroutineScope()
                    QuickAccessSettingHeader(
                        isFavorite = quickAccessSetting in quickAccessSettings.value,
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
            }
        }

        when (setting) {
            Setting.AlgorithmImplementation -> AlgorithmImplementationUi()
            Setting.CellStatePreview -> CellStatePreviewUi()
            Setting.DarkThemeConfig -> DarkThemeConfigUi()
            Setting.CellShapeConfig -> CellShapeConfigUi()
            Setting.DisableAGSL -> DisableAGSLUi()
            Setting.DisableOpenGL -> DisableOpenGLUi()
        }
    }
}

context(SettingUiEntryPoint)
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
        },
        modifier = modifier,
        onOpenInSettingsClicked = onOpenInSettingsClicked,
    )
}
