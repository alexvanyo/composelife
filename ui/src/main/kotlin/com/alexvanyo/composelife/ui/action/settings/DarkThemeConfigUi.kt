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

import androidx.compose.foundation.layout.Box
import androidx.compose.runtime.Composable
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.ui.Modifier
import androidx.compose.ui.res.stringResource
import androidx.compose.ui.tooling.preview.Preview
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.preferences.DarkThemeConfig
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.ui.R
import com.alexvanyo.composelife.ui.component.DropdownOption
import com.alexvanyo.composelife.ui.component.GameOfLifeProgressIndicator
import com.alexvanyo.composelife.ui.component.GameOfLifeProgressIndicatorEntryPoint
import com.alexvanyo.composelife.ui.component.TextFieldDropdown
import com.alexvanyo.composelife.ui.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.theme.ComposeLifeTheme
import com.livefront.sealedenum.GenSealedEnum
import dagger.hilt.EntryPoint
import dagger.hilt.InstallIn
import dagger.hilt.android.components.ActivityComponent
import kotlinx.coroutines.launch

@EntryPoint
@InstallIn(ActivityComponent::class)
interface DarkThemeConfigUiEntryPoint :
    ComposeLifePreferencesProvider,
    GameOfLifeProgressIndicatorEntryPoint

context(DarkThemeConfigUiEntryPoint)
@Composable
fun DarkThemeConfigUi(
    modifier: Modifier = Modifier,
) {
    DarkThemeConfigUi(
        darkThemeConfigState = composeLifePreferences.darkThemeConfigState,
        setDarkThemeConfig = composeLifePreferences::setDarkThemeConfig,
        modifier = modifier,
    )
}

context(GameOfLifeProgressIndicatorEntryPoint)
@Composable
fun DarkThemeConfigUi(
    darkThemeConfigState: ResourceState<DarkThemeConfig>,
    setDarkThemeConfig: suspend (DarkThemeConfig) -> Unit,
    modifier: Modifier = Modifier,
) {
    Box(modifier = modifier) {
        when (darkThemeConfigState) {
            ResourceState.Loading, is ResourceState.Failure -> {
                GameOfLifeProgressIndicator()
            }

            is ResourceState.Success -> {
                val currentDarkThemeConfig = darkThemeConfigState.value
                val coroutineScope = rememberCoroutineScope()

                TextFieldDropdown(
                    label = stringResource(R.string.dark_theme_config),
                    currentValue = when (currentDarkThemeConfig) {
                        DarkThemeConfig.FollowSystem -> DarkThemeConfigDropdownOption.AFollowSystem
                        DarkThemeConfig.Dark -> DarkThemeConfigDropdownOption.Dark
                        DarkThemeConfig.Light -> DarkThemeConfigDropdownOption.Light
                    },
                    allValues = DarkThemeConfigDropdownOption.values,
                    setValue = { option ->
                        coroutineScope.launch {
                            setDarkThemeConfig(
                                when (option) {
                                    DarkThemeConfigDropdownOption.AFollowSystem -> DarkThemeConfig.FollowSystem
                                    DarkThemeConfigDropdownOption.Dark -> DarkThemeConfig.Dark
                                    DarkThemeConfigDropdownOption.Light -> DarkThemeConfig.Light
                                },
                            )
                        }
                    },
                )
            }
        }
    }
}

sealed interface DarkThemeConfigDropdownOption : DropdownOption {
    /**
     * TODO: Rename to FollowSystem once sealed enum generation is fixed on Kotlin 1.7.0
     */
    object AFollowSystem : DarkThemeConfigDropdownOption {
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

@Preview
@Composable
fun DarkThemeConfigUiLoadingPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            DarkThemeConfigUi(
                darkThemeConfigState = ResourceState.Loading,
                setDarkThemeConfig = {},
            )
        }
    }
}

@Preview
@Composable
fun DarkThemeConfigUiLoadedPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            DarkThemeConfigUi(
                darkThemeConfigState = ResourceState.Success(DarkThemeConfig.FollowSystem),
                setDarkThemeConfig = {},
            )
        }
    }
}
