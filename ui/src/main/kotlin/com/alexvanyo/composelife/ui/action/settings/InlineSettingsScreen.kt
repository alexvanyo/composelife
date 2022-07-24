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

import androidx.compose.animation.AnimatedContent
import androidx.compose.animation.AnimatedVisibility
import androidx.compose.animation.ExperimentalAnimationApi
import androidx.compose.foundation.ScrollState
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.layout.padding
import androidx.compose.foundation.rememberScrollState
import androidx.compose.foundation.verticalScroll
import androidx.compose.material3.Surface
import androidx.compose.material3.Text
import androidx.compose.material3.TextButton
import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.key
import androidx.compose.runtime.remember
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.res.stringResource
import androidx.compose.ui.text.style.TextAlign
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.preferences.QuickAccessSetting
import com.alexvanyo.composelife.preferences.TestComposeLifePreferences
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.ordinal
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.snapshotstateset.toMutableStateSet
import com.alexvanyo.composelife.ui.R
import com.alexvanyo.composelife.ui.component.GameOfLifeProgressIndicator
import com.alexvanyo.composelife.ui.component.GameOfLifeProgressIndicatorEntryPoint
import com.alexvanyo.composelife.ui.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.theme.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.ThemePreviews
import dagger.hilt.EntryPoint
import dagger.hilt.InstallIn
import dagger.hilt.android.components.ActivityComponent

@EntryPoint
@InstallIn(ActivityComponent::class)
interface InlineSettingsScreenEntryPoint :
    ComposeLifePreferencesProvider,
    GameOfLifeProgressIndicatorEntryPoint,
    SettingUiEntryPoint

context(InlineSettingsScreenEntryPoint)
@OptIn(ExperimentalAnimationApi::class)
@Composable
fun InlineSettingsScreen(
    onSeeMoreClicked: () -> Unit,
    onOpenInSettingsClicked: (Setting) -> Unit,
    modifier: Modifier = Modifier,
    scrollState: ScrollState = rememberScrollState(),
) {
    Column(
        modifier = modifier
            .fillMaxWidth()
            .verticalScroll(scrollState),
        horizontalAlignment = Alignment.CenterHorizontally,
    ) {
        when (val quickAccessSettingsState = composeLifePreferences.quickAccessSettings) {
            ResourceState.Loading, is ResourceState.Failure -> {
                GameOfLifeProgressIndicator()
            }
            is ResourceState.Success -> {
                val quickAccessSettings = quickAccessSettingsState.value
                /**
                 * The list of previously known quick access settings, used to smoothly animate out upon removing.
                 */
                val previouslyKnownQuickAccessSettings = remember {
                    quickAccessSettings.toMutableStateSet()
                }
                /**
                 * Compute all known quick access settings. The order is important here for smooth animations:
                 * We sort into the [QuickAccessSetting] ordinal order.
                 */
                val allKnownQuickAccessSettings = (previouslyKnownQuickAccessSettings + quickAccessSettings)
                    .sortedBy(QuickAccessSetting::ordinal)

                AnimatedContent(
                    targetState = quickAccessSettings.isEmpty(),
                ) { showQuickAccessInfo ->
                    if (showQuickAccessInfo) {
                        Text(
                            text = stringResource(id = R.string.quick_settings_info),
                            textAlign = TextAlign.Center,
                            modifier = Modifier.padding(horizontal = 16.dp),
                        )
                    } else {
                        Column {
                            allKnownQuickAccessSettings.forEach { quickAccessSetting ->
                                key(quickAccessSetting) {
                                    AnimatedVisibility(
                                        visible = quickAccessSetting in quickAccessSettings,
                                    ) {
                                        SettingUi(
                                            quickAccessSetting = quickAccessSetting,
                                            onOpenInSettingsClicked = onOpenInSettingsClicked,
                                            modifier = Modifier.padding(horizontal = 16.dp),
                                        )
                                    }
                                }
                            }
                        }
                    }
                }

                // Sync the all known quick access settings back to `previouslyKnownQuickAccessSettings`
                LaunchedEffect(allKnownQuickAccessSettings) {
                    previouslyKnownQuickAccessSettings.addAll(allKnownQuickAccessSettings)
                }
            }
        }

        TextButton(
            onClick = onSeeMoreClicked,
        ) {
            Text(text = stringResource(R.string.see_all))
        }
    }
}

@ThemePreviews
@Composable
fun InlineSettingsScreenNoQuickAccessPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            Surface {
                InlineSettingsScreen(
                    onSeeMoreClicked = {},
                    onOpenInSettingsClicked = {},
                )
            }
        }
    }
}

@ThemePreviews
@Composable
fun InlineSettingsScreenWithQuickAccessPreview() {
    WithPreviewDependencies(
        composeLifePreferences = TestComposeLifePreferences.Loaded(
            quickAccessSettings = setOf(
                QuickAccessSetting.DarkThemeConfig,
                QuickAccessSetting.CellShapeConfig,
            ),
        ),
    ) {
        ComposeLifeTheme {
            Surface {
                InlineSettingsScreen(
                    onSeeMoreClicked = {},
                    onOpenInSettingsClicked = {},
                )
            }
        }
    }
}
