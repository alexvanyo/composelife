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

package com.alexvanyo.composelife.ui.settings

import androidx.compose.animation.ExperimentalSharedTransitionApi
import androidx.compose.animation.SharedTransitionLayout
import androidx.compose.foundation.layout.BoxWithConstraints
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.material3.Surface
import androidx.compose.runtime.Composable
import androidx.compose.ui.Modifier
import androidx.compose.ui.unit.IntSize
import androidx.compose.ui.unit.toSize
import androidx.window.core.layout.WindowSizeClass
import androidx.window.core.layout.WindowSizeClass.Companion.BREAKPOINTS_V1
import androidx.window.core.layout.computeWindowSizeClass
import com.airbnb.android.showkase.annotation.ShowkaseComposable
import com.alexvanyo.composelife.ui.mobile.ComposeLifeTheme
import com.alexvanyo.composelife.ui.mobile.component.ListDetailInfo
import com.alexvanyo.composelife.ui.settings.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.util.MobileDevicePreviews

@ShowkaseComposable
@OptIn(ExperimentalSharedTransitionApi::class)
@MobileDevicePreviews
@Composable
fun FullscreenSettingsPaneListPreview(modifier: Modifier = Modifier) {
    WithPreviewDependencies {
        ComposeLifeTheme {
            BoxWithConstraints(modifier) {
                val size = IntSize(constraints.maxWidth, constraints.maxHeight).toSize()
                val windowSizeClass = BREAKPOINTS_V1.computeWindowSizeClass(
                    widthDp = size.width,
                    heightDp = size.height,
                )

                val fullscreenSettingsListPaneState = object : FullscreenSettingsListPaneState {
                    override val settingsCategory = SettingsCategory.Algorithm
                    override val isListVisible = true
                    override val isDetailVisible =
                        windowSizeClass.isWidthAtLeastBreakpoint(WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND)
                }
                val fullscreenSettingsDetailPaneState =
                    object : FullscreenSettingsDetailPaneState, ListDetailInfo by fullscreenSettingsListPaneState {
                        override val settingsCategory = SettingsCategory.Algorithm
                        override val settingToScrollTo: Setting? = null
                        override fun onFinishedScrollingToSetting() = Unit
                    }

                Surface {
                    SharedTransitionLayout {
                        FullscreenSettingsPane(
                            fullscreenSettingsListPaneState = fullscreenSettingsListPaneState,
                            fullscreenSettingsDetailPaneState = fullscreenSettingsDetailPaneState,
                            onBackButtonPressed = {},
                            setSettingsCategory = {},
                            modifier = Modifier.fillMaxSize(),
                        )
                    }
                }
            }
        }
    }
}

@ShowkaseComposable
@OptIn(ExperimentalSharedTransitionApi::class)
@MobileDevicePreviews
@Composable
fun FullscreenSettingsPaneAlgorithmPreview(modifier: Modifier = Modifier) {
    WithPreviewDependencies {
        ComposeLifeTheme {
            BoxWithConstraints(modifier) {
                val size = IntSize(constraints.maxWidth, constraints.maxHeight).toSize()
                val windowSizeClass = BREAKPOINTS_V1.computeWindowSizeClass(
                    widthDp = size.width,
                    heightDp = size.height,
                )

                val fullscreenSettingsListPaneState = object : FullscreenSettingsListPaneState {
                    override val settingsCategory = SettingsCategory.Algorithm
                    override val isListVisible =
                        windowSizeClass.isWidthAtLeastBreakpoint(WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND)
                    override val isDetailVisible = true
                }
                val fullscreenSettingsDetailPaneState =
                    object : FullscreenSettingsDetailPaneState, ListDetailInfo by fullscreenSettingsListPaneState {
                        override val settingsCategory = SettingsCategory.Algorithm
                        override val settingToScrollTo: Setting? = null
                        override fun onFinishedScrollingToSetting() = Unit
                    }

                Surface {
                    SharedTransitionLayout {
                        FullscreenSettingsPane(
                            fullscreenSettingsListPaneState = fullscreenSettingsListPaneState,
                            fullscreenSettingsDetailPaneState = fullscreenSettingsDetailPaneState,
                            onBackButtonPressed = {},
                            setSettingsCategory = {},
                            modifier = Modifier.fillMaxSize(),
                        )
                    }
                }
            }
        }
    }
}

@ShowkaseComposable
@OptIn(ExperimentalSharedTransitionApi::class)
@MobileDevicePreviews
@Composable
internal fun FullscreenSettingsPaneVisualPreview(modifier: Modifier = Modifier) {
    WithPreviewDependencies {
        ComposeLifeTheme {
            BoxWithConstraints(modifier) {
                val size = IntSize(constraints.maxWidth, constraints.maxHeight).toSize()
                val windowSizeClass = BREAKPOINTS_V1.computeWindowSizeClass(
                    widthDp = size.width,
                    heightDp = size.height,
                )

                val fullscreenSettingsListPaneState = object : FullscreenSettingsListPaneState {
                    override val settingsCategory = SettingsCategory.Visual
                    override val isListVisible =
                        windowSizeClass.isWidthAtLeastBreakpoint(WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND)
                    override val isDetailVisible = true
                }
                val fullscreenSettingsDetailPaneState =
                    object : FullscreenSettingsDetailPaneState, ListDetailInfo by fullscreenSettingsListPaneState {
                        override val settingsCategory = SettingsCategory.Visual
                        override val settingToScrollTo: Setting? = null
                        override fun onFinishedScrollingToSetting() = Unit
                    }

                Surface {
                    SharedTransitionLayout {
                        FullscreenSettingsPane(
                            fullscreenSettingsListPaneState = fullscreenSettingsListPaneState,
                            fullscreenSettingsDetailPaneState = fullscreenSettingsDetailPaneState,
                            onBackButtonPressed = {},
                            setSettingsCategory = {},
                            modifier = Modifier.fillMaxSize(),
                        )
                    }
                }
            }
        }
    }
}

@ShowkaseComposable
@OptIn(ExperimentalSharedTransitionApi::class)
@MobileDevicePreviews
@Composable
internal fun FullscreenSettingsPaneFeatureFlagsPreview(modifier: Modifier = Modifier) {
    WithPreviewDependencies {
        ComposeLifeTheme {
            BoxWithConstraints(modifier) {
                val size = IntSize(constraints.maxWidth, constraints.maxHeight).toSize()
                val windowSizeClass = BREAKPOINTS_V1.computeWindowSizeClass(
                    widthDp = size.width,
                    heightDp = size.height,
                )

                val fullscreenSettingsListPaneState = object : FullscreenSettingsListPaneState {
                    override val settingsCategory = SettingsCategory.FeatureFlags
                    override val isListVisible =
                        windowSizeClass.isWidthAtLeastBreakpoint(WindowSizeClass.WIDTH_DP_MEDIUM_LOWER_BOUND)
                    override val isDetailVisible = true
                }
                val fullscreenSettingsDetailPaneState =
                    object : FullscreenSettingsDetailPaneState, ListDetailInfo by fullscreenSettingsListPaneState {
                        override val settingsCategory = SettingsCategory.FeatureFlags
                        override val settingToScrollTo: Setting? = null
                        override fun onFinishedScrollingToSetting() = Unit
                    }

                Surface {
                    SharedTransitionLayout {
                        FullscreenSettingsPane(
                            fullscreenSettingsListPaneState = fullscreenSettingsListPaneState,
                            fullscreenSettingsDetailPaneState = fullscreenSettingsDetailPaneState,
                            onBackButtonPressed = {},
                            setSettingsCategory = {},
                            modifier = Modifier.fillMaxSize(),
                        )
                    }
                }
            }
        }
    }
}
