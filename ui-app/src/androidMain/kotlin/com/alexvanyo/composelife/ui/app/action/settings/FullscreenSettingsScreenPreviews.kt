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
import com.alexvanyo.composelife.ui.app.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.app.theme.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.MobileDevicePreviews

@OptIn(ExperimentalMaterial3WindowSizeClassApi::class)
@MobileDevicePreviews
@Composable
fun FullscreenSettingsScreenListPreview(modifier: Modifier = Modifier) {
    WithPreviewDependencies {
        ComposeLifeTheme {
            BoxWithConstraints(modifier) {
                val size = IntSize(constraints.maxWidth, constraints.maxHeight).toSize()
                Surface {
                    FullscreenSettingsScreen(
                        windowSizeClass = WindowSizeClass.calculateFromSize(size, LocalDensity.current),
                        navEntryValue = ComposeLifeNavigation.FullscreenSettings(
                            initialSettingsCategory = SettingsCategory.Algorithm,
                            initialShowDetails = false,
                            initialSettingToScrollTo = null,
                        ),
                        onBackButtonPressed = {},
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
fun FullscreenSettingsScreenAlgorithmPreview(modifier: Modifier = Modifier) {
    WithPreviewDependencies {
        ComposeLifeTheme {
            BoxWithConstraints(modifier) {
                val size = IntSize(constraints.maxWidth, constraints.maxHeight).toSize()
                Surface {
                    FullscreenSettingsScreen(
                        windowSizeClass = WindowSizeClass.calculateFromSize(size, LocalDensity.current),
                        navEntryValue = ComposeLifeNavigation.FullscreenSettings(
                            initialSettingsCategory = SettingsCategory.Algorithm,
                            initialShowDetails = true,
                            initialSettingToScrollTo = null,
                        ),
                        onBackButtonPressed = {},
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
fun FullscreenSettingsScreenVisualPreview(modifier: Modifier = Modifier) {
    WithPreviewDependencies {
        ComposeLifeTheme {
            BoxWithConstraints(modifier) {
                val size = IntSize(constraints.maxWidth, constraints.maxHeight).toSize()
                Surface {
                    FullscreenSettingsScreen(
                        windowSizeClass = WindowSizeClass.calculateFromSize(size, LocalDensity.current),
                        navEntryValue = ComposeLifeNavigation.FullscreenSettings(
                            initialSettingsCategory = SettingsCategory.Visual,
                            initialShowDetails = true,
                            initialSettingToScrollTo = null,
                        ),
                        onBackButtonPressed = {},
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
fun FullscreenSettingsScreenFeatureFlagsPreview(modifier: Modifier = Modifier) {
    WithPreviewDependencies {
        ComposeLifeTheme {
            BoxWithConstraints(modifier) {
                val size = IntSize(constraints.maxWidth, constraints.maxHeight).toSize()
                Surface {
                    FullscreenSettingsScreen(
                        windowSizeClass = WindowSizeClass.calculateFromSize(size, LocalDensity.current),
                        navEntryValue = ComposeLifeNavigation.FullscreenSettings(
                            initialSettingsCategory = SettingsCategory.FeatureFlags,
                            initialShowDetails = true,
                            initialSettingToScrollTo = null,
                        ),
                        onBackButtonPressed = {},
                        modifier = Modifier.fillMaxSize(),
                    )
                }
            }
        }
    }
}
