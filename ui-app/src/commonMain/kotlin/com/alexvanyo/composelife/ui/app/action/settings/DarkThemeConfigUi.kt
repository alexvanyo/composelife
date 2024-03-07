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
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResource
import com.alexvanyo.composelife.preferences.DarkThemeConfig
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.di.LoadedComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.setDarkThemeConfig
import com.alexvanyo.composelife.ui.app.component.DropdownOption
import com.alexvanyo.composelife.ui.app.component.TextFieldDropdown
import com.alexvanyo.composelife.ui.app.resources.DarkTheme
import com.alexvanyo.composelife.ui.app.resources.DarkThemeConfig
import com.alexvanyo.composelife.ui.app.resources.FollowSystem
import com.alexvanyo.composelife.ui.app.resources.LightTheme
import com.alexvanyo.composelife.ui.app.resources.Strings
import com.livefront.sealedenum.GenSealedEnum
import kotlinx.collections.immutable.toImmutableList
import kotlinx.coroutines.launch

interface DarkThemeConfigUiInjectEntryPoint :
    ComposeLifePreferencesProvider

interface DarkThemeConfigUiLocalEntryPoint :
    LoadedComposeLifePreferencesProvider

context(DarkThemeConfigUiInjectEntryPoint, DarkThemeConfigUiLocalEntryPoint)
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
            label = parameterizedStringResource(Strings.DarkThemeConfig),
            currentValue = when (darkThemeConfig) {
                DarkThemeConfig.FollowSystem -> DarkThemeConfigDropdownOption.FollowSystem
                DarkThemeConfig.Dark -> DarkThemeConfigDropdownOption.Dark
                DarkThemeConfig.Light -> DarkThemeConfigDropdownOption.Light
            },
            allValues = DarkThemeConfigDropdownOption.values.toImmutableList(),
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
    data object FollowSystem : DarkThemeConfigDropdownOption {
        override val displayText: ParameterizedString = Strings.FollowSystem
    }
    data object Dark : DarkThemeConfigDropdownOption {
        override val displayText: ParameterizedString = Strings.DarkTheme
    }
    data object Light : DarkThemeConfigDropdownOption {
        override val displayText: ParameterizedString = Strings.LightTheme
    }

    @GenSealedEnum
    companion object
}
