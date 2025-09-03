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

package com.alexvanyo.composelife.ui.settings

import androidx.compose.foundation.layout.Box
import androidx.compose.runtime.Composable
import androidx.compose.runtime.Immutable
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.ui.Modifier
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResource
import com.alexvanyo.composelife.preferences.ComposeLifePreferences
import com.alexvanyo.composelife.preferences.DarkThemeConfig
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferencesHolder
import com.alexvanyo.composelife.preferences.setDarkThemeConfig
import com.alexvanyo.composelife.ui.mobile.component.DropdownOption
import com.alexvanyo.composelife.ui.mobile.component.TextFieldDropdown
import com.alexvanyo.composelife.ui.settings.resources.DarkTheme
import com.alexvanyo.composelife.ui.settings.resources.DarkThemeConfig
import com.alexvanyo.composelife.ui.settings.resources.FollowSystem
import com.alexvanyo.composelife.ui.settings.resources.LightTheme
import com.alexvanyo.composelife.ui.settings.resources.Strings
import com.livefront.sealedenum.GenSealedEnum
import dev.zacsweers.metro.Inject
import kotlinx.collections.immutable.toImmutableList
import kotlinx.coroutines.launch

// region templated-ctx
@Immutable
@Inject
class DarkThemeConfigUiCtx(
    private val preferencesHolder: LoadedComposeLifePreferencesHolder,
    private val composeLifePreferences: ComposeLifePreferences,
) {
    @Suppress("ComposableNaming")
    @Composable
    operator fun invoke(
        modifier: Modifier = Modifier,
    ) = lambda(preferencesHolder, composeLifePreferences, modifier)

    companion object {
        private val lambda:
            @Composable context(LoadedComposeLifePreferencesHolder, ComposeLifePreferences) (
                modifier: Modifier,
            ) -> Unit =
            { modifier ->
                DarkThemeConfigUi(modifier)
            }
    }
}

context(ctx: DarkThemeConfigUiCtx)
@Composable
fun DarkThemeConfigUi(
    modifier: Modifier = Modifier,
) = ctx(modifier)
// endregion templated-ctx

context(
    preferencesHolder: LoadedComposeLifePreferencesHolder,
composeLifePreferences: ComposeLifePreferences,
)
@Composable
private fun DarkThemeConfigUi(
    modifier: Modifier = Modifier,
) {
    DarkThemeConfigUi(
        darkThemeConfig = preferencesHolder.preferences.darkThemeConfig,
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
            allValues = DarkThemeConfigDropdownOption._values.toImmutableList(),
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

expect val DarkThemeConfigDropdownOption.Companion._values: List<DarkThemeConfigDropdownOption>
