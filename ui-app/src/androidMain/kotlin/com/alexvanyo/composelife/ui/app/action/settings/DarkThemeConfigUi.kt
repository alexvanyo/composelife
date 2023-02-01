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

import androidx.compose.foundation.layout.Box
import androidx.compose.runtime.Composable
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.ui.Modifier
import androidx.compose.ui.res.stringResource
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.preferences.DarkThemeConfig
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.di.LoadedComposeLifePreferencesProvider
import com.alexvanyo.composelife.ui.app.R
import com.alexvanyo.composelife.ui.app.component.DropdownOption
import com.alexvanyo.composelife.ui.app.component.TextFieldDropdown
import com.alexvanyo.composelife.ui.app.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.app.theme.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.ThemePreviews
import com.livefront.sealedenum.GenSealedEnum
import dagger.hilt.EntryPoint
import dagger.hilt.InstallIn
import dagger.hilt.android.components.ActivityComponent
import kotlinx.coroutines.launch

@EntryPoint
@InstallIn(ActivityComponent::class)
interface DarkThemeConfigUiHiltEntryPoint :
    ComposeLifePreferencesProvider

interface DarkThemeConfigUiLocalEntryPoint :
    LoadedComposeLifePreferencesProvider

context(DarkThemeConfigUiHiltEntryPoint, DarkThemeConfigUiLocalEntryPoint)
@Composable
fun DarkThemeConfigUi(
    modifier: Modifier = Modifier,
) {
    DarkThemeConfigUi(
        darkThemeConfig = preferences.darkThemeConfig,
        setDarkThemeConfig = composeLifePreferences::setDarkThemeConfig,
        modifier = modifier,
    )
}

@Composable
fun DarkThemeConfigUi(
    darkThemeConfig: DarkThemeConfig,
    setDarkThemeConfig: suspend (DarkThemeConfig) -> Unit,
    modifier: Modifier = Modifier,
) {
    Box(modifier = modifier) {
        val coroutineScope = rememberCoroutineScope()

        TextFieldDropdown(
            label = stringResource(R.string.dark_theme_config),
            currentValue = when (darkThemeConfig) {
                DarkThemeConfig.FollowSystem -> DarkThemeConfigDropdownOption.FollowSystem
                DarkThemeConfig.Dark -> DarkThemeConfigDropdownOption.Dark
                DarkThemeConfig.Light -> DarkThemeConfigDropdownOption.Light
            },
            allValues = DarkThemeConfigDropdownOption.values,
            setValue = { option ->
                coroutineScope.launch {
                    setDarkThemeConfig(
                        when (option) {
                            DarkThemeConfigDropdownOption.FollowSystem -> DarkThemeConfig.FollowSystem
                            DarkThemeConfigDropdownOption.Dark -> DarkThemeConfig.Dark
                            DarkThemeConfigDropdownOption.Light -> DarkThemeConfig.Light
                        },
                    )
                }
            },
        )
    }
}

sealed interface DarkThemeConfigDropdownOption : DropdownOption {
    object FollowSystem : DarkThemeConfigDropdownOption {
        override val displayText: ParameterizedString = ParameterizedString(R.string.follow_system)
    }
    object Dark : DarkThemeConfigDropdownOption {
        override val displayText: ParameterizedString = ParameterizedString(R.string.dark_theme)
    }
    object Light : DarkThemeConfigDropdownOption {
        override val displayText: ParameterizedString = ParameterizedString(R.string.light_theme)
    }

    @GenSealedEnum
    companion object
}

@ThemePreviews
@Composable
fun DarkThemeConfigUiFollowSystemPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            DarkThemeConfigUi(
                darkThemeConfig = DarkThemeConfig.FollowSystem,
                setDarkThemeConfig = {},
            )
        }
    }
}
