/*
 * Copyright 2024 The Android Open Source Project
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

package com.alexvanyo.composelife.ui.app.action.settings

import androidx.compose.foundation.layout.BoxWithConstraints
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.material3.Surface
import androidx.compose.material3.windowsizeclass.ExperimentalMaterial3WindowSizeClassApi
import androidx.compose.material3.windowsizeclass.WindowSizeClass
import androidx.compose.runtime.Composable
import androidx.compose.ui.Modifier
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.unit.IntSize
import androidx.compose.ui.unit.toSize
import com.alexvanyo.composelife.ui.app.ComposeLifeNavigation
import com.alexvanyo.composelife.ui.app.ComposeLifeUiNavigation
import com.alexvanyo.composelife.ui.app.component.ListDetailPaneScaffold
import com.alexvanyo.composelife.ui.app.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.app.theme.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.MobileDevicePreviews

context(FullscreenSettingsDetailPaneInjectEntryPoint, FullscreenSettingsDetailPaneLocalEntryPoint)
@Composable
private fun FullscreenSettingsPanePreview(
    listNavValue: ComposeLifeUiNavigation.FullscreenSettingsList,
    detailsNavValue: ComposeLifeUiNavigation.FullscreenSettingsDetail,
    modifier: Modifier = Modifier,
) {
    ListDetailPaneScaffold(
        showList = listNavValue.isListVisible,
        showDetail = listNavValue.isDetailVisible,
        listContent = {
            FullscreenSettingsListPane(
                navEntryValue = listNavValue,
                setSettingsCategory = {},
                onBackButtonPressed = {},
            )
        },
        detailContent = {
            FullscreenSettingsDetailPane(
                navEntryValue = detailsNavValue,
                onBackButtonPressed = {},
            )
        },
        onBackButtonPressed = {},
        modifier = modifier,
    )
}

@OptIn(ExperimentalMaterial3WindowSizeClassApi::class)
@MobileDevicePreviews
@Composable
fun FullscreenSettingsPaneListPreview(modifier: Modifier = Modifier) {
    WithPreviewDependencies {
        ComposeLifeTheme {
            BoxWithConstraints(modifier) {
                val size = IntSize(constraints.maxWidth, constraints.maxHeight).toSize()
                val windowSizeClass = WindowSizeClass.calculateFromSize(size, LocalDensity.current)

                val listNavValue = ComposeLifeUiNavigation.FullscreenSettingsList(
                    nav = ComposeLifeNavigation.FullscreenSettingsList(
                        initialSettingsCategory = SettingsCategory.Algorithm,
                    ),
                    windowSizeClass = windowSizeClass,
                    isDetailPresent = false,
                )
                val detailsNavValue = ComposeLifeUiNavigation.FullscreenSettingsDetail(
                    nav = ComposeLifeNavigation.FullscreenSettingsDetail(
                        settingsCategory = SettingsCategory.Algorithm,
                        initialSettingToScrollTo = null,
                    ),
                    listDetailInfo = listNavValue,
                )

                Surface {
                    FullscreenSettingsPanePreview(
                        listNavValue = listNavValue,
                        detailsNavValue = detailsNavValue,
                        modifier = Modifier.fillMaxSize(),
                    )
                }
            }
        }
    }
}

@OptIn(ExperimentalMaterial3WindowSizeClassApi::class)
@MobileDevicePreviews
@Composable
fun FullscreenSettingsPaneAlgorithmPreview(modifier: Modifier = Modifier) {
    WithPreviewDependencies {
        ComposeLifeTheme {
            BoxWithConstraints(modifier) {
                val size = IntSize(constraints.maxWidth, constraints.maxHeight).toSize()
                val windowSizeClass = WindowSizeClass.calculateFromSize(size, LocalDensity.current)

                val listNavValue = ComposeLifeUiNavigation.FullscreenSettingsList(
                    nav = ComposeLifeNavigation.FullscreenSettingsList(
                        initialSettingsCategory = SettingsCategory.Algorithm,
                    ),
                    windowSizeClass = windowSizeClass,
                    isDetailPresent = true,
                )
                val detailsNavValue = ComposeLifeUiNavigation.FullscreenSettingsDetail(
                    nav = ComposeLifeNavigation.FullscreenSettingsDetail(
                        settingsCategory = SettingsCategory.Algorithm,
                        initialSettingToScrollTo = null,
                    ),
                    listDetailInfo = listNavValue,
                )

                Surface {
                    FullscreenSettingsPanePreview(
                        listNavValue = listNavValue,
                        detailsNavValue = detailsNavValue,
                        modifier = Modifier.fillMaxSize(),
                    )
                }
            }
        }
    }
}

@OptIn(ExperimentalMaterial3WindowSizeClassApi::class)
@MobileDevicePreviews
@Composable
fun FullscreenSettingsPaneVisualPreview(modifier: Modifier = Modifier) {
    WithPreviewDependencies {
        ComposeLifeTheme {
            BoxWithConstraints(modifier) {
                val size = IntSize(constraints.maxWidth, constraints.maxHeight).toSize()
                val windowSizeClass = WindowSizeClass.calculateFromSize(size, LocalDensity.current)

                val listNavValue = ComposeLifeUiNavigation.FullscreenSettingsList(
                    nav = ComposeLifeNavigation.FullscreenSettingsList(
                        initialSettingsCategory = SettingsCategory.Visual,
                    ),
                    windowSizeClass = windowSizeClass,
                    isDetailPresent = true,
                )
                val detailsNavValue = ComposeLifeUiNavigation.FullscreenSettingsDetail(
                    nav = ComposeLifeNavigation.FullscreenSettingsDetail(
                        settingsCategory = SettingsCategory.Visual,
                        initialSettingToScrollTo = null,
                    ),
                    listDetailInfo = listNavValue,
                )

                Surface {
                    FullscreenSettingsPanePreview(
                        listNavValue = listNavValue,
                        detailsNavValue = detailsNavValue,
                        modifier = Modifier.fillMaxSize(),
                    )
                }
            }
        }
    }
}

@OptIn(ExperimentalMaterial3WindowSizeClassApi::class)
@MobileDevicePreviews
@Composable
fun FullscreenSettingsPaneFeatureFlagsPreview(modifier: Modifier = Modifier) {
    WithPreviewDependencies {
        ComposeLifeTheme {
            BoxWithConstraints(modifier) {
                val size = IntSize(constraints.maxWidth, constraints.maxHeight).toSize()
                val windowSizeClass = WindowSizeClass.calculateFromSize(size, LocalDensity.current)

                val listNavValue = ComposeLifeUiNavigation.FullscreenSettingsList(
                    nav = ComposeLifeNavigation.FullscreenSettingsList(
                        initialSettingsCategory = SettingsCategory.FeatureFlags,
                    ),
                    windowSizeClass = windowSizeClass,
                    isDetailPresent = true,
                )
                val detailsNavValue = ComposeLifeUiNavigation.FullscreenSettingsDetail(
                    nav = ComposeLifeNavigation.FullscreenSettingsDetail(
                        settingsCategory = SettingsCategory.FeatureFlags,
                        initialSettingToScrollTo = null,
                    ),
                    listDetailInfo = listNavValue,
                )

                Surface {
                    FullscreenSettingsPanePreview(
                        listNavValue = listNavValue,
                        detailsNavValue = detailsNavValue,
                        modifier = Modifier.fillMaxSize(),
                    )
                }
            }
        }
    }
}
