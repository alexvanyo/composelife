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

import androidx.compose.animation.ExperimentalSharedTransitionApi
import androidx.compose.animation.SharedTransitionScope
import androidx.compose.animation.core.animateDpAsState
import androidx.compose.foundation.ScrollState
import androidx.compose.foundation.layout.Arrangement
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.WindowInsets
import androidx.compose.foundation.layout.WindowInsetsSides
import androidx.compose.foundation.layout.consumeWindowInsets
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.layout.height
import androidx.compose.foundation.layout.only
import androidx.compose.foundation.layout.padding
import androidx.compose.foundation.layout.safeDrawing
import androidx.compose.foundation.layout.safeDrawingPadding
import androidx.compose.foundation.layout.windowInsetsPadding
import androidx.compose.foundation.rememberScrollState
import androidx.compose.foundation.verticalScroll
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.automirrored.filled.ArrowBack
import androidx.compose.material3.ExperimentalMaterial3Api
import androidx.compose.material3.Icon
import androidx.compose.material3.IconButton
import androidx.compose.material3.MaterialTheme
import androidx.compose.material3.PlainTooltip
import androidx.compose.material3.Surface
import androidx.compose.material3.Text
import androidx.compose.material3.TooltipBox
import androidx.compose.material3.TooltipDefaults
import androidx.compose.material3.pulltorefresh.PullToRefreshBox
import androidx.compose.material3.rememberTooltipState
import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.runtime.setValue
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.layout.LayoutCoordinates
import androidx.compose.ui.layout.boundsInParent
import androidx.compose.ui.layout.onPlaced
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResource
import com.alexvanyo.composelife.ui.mobile.component.ListDetailInfo
import com.alexvanyo.composelife.ui.mobile.component.LocalBackgroundColor
import com.alexvanyo.composelife.ui.settings.resources.Back
import com.alexvanyo.composelife.ui.settings.resources.Strings
import com.alexvanyo.composelife.ui.util.trySharedBounds
import kotlinx.coroutines.delay
import kotlinx.coroutines.launch
import kotlin.math.roundToInt

interface FullscreenSettingsDetailPaneInjectEntryPoint :
    SettingUiInjectEntryPoint

interface FullscreenSettingsDetailPaneLocalEntryPoint :
    SettingUiLocalEntryPoint

context(_: FullscreenSettingsDetailPaneInjectEntryPoint, _: FullscreenSettingsDetailPaneLocalEntryPoint)
@Composable
fun FullscreenSettingsDetailPane(
    fullscreenSettingsDetailPaneState: FullscreenSettingsDetailPaneState,
    onBackButtonPressed: () -> Unit,
    modifier: Modifier = Modifier,
) {
    SettingsCategoryDetail(
        settingsCategory = fullscreenSettingsDetailPaneState.settingsCategory,
        detailScrollState = rememberScrollState(),
        showAppBar = !(
            fullscreenSettingsDetailPaneState.isDetailVisible &&
                fullscreenSettingsDetailPaneState.isListVisible
            ),
        onBackButtonPressed = onBackButtonPressed,
        settingToScrollTo = fullscreenSettingsDetailPaneState.settingToScrollTo,
        onFinishedScrollingToSetting = fullscreenSettingsDetailPaneState::onFinishedScrollingToSetting,
        modifier = modifier,
    )
}

context(_: SettingUiInjectEntryPoint, _: SettingUiLocalEntryPoint)
@OptIn(ExperimentalMaterial3Api::class, ExperimentalSharedTransitionApi::class)
@Suppress("LongMethod", "LongParameterList")
@Composable
private fun SettingsCategoryDetail(
    settingsCategory: SettingsCategory,
    detailScrollState: ScrollState,
    showAppBar: Boolean,
    onBackButtonPressed: () -> Unit,
    settingToScrollTo: Setting?,
    onFinishedScrollingToSetting: () -> Unit,
    modifier: Modifier = Modifier,
) {
    when (settingsCategory) {
        SettingsCategory.Algorithm,
        SettingsCategory.FeatureFlags,
        SettingsCategory.Visual,
        -> {
            StandardSettingsCategoryDetail(
                settingsCategory = settingsCategory,
                detailScrollState = detailScrollState,
                showAppBar = showAppBar,
                onBackButtonPressed = onBackButtonPressed,
                settingToScrollTo = settingToScrollTo,
                onFinishedScrollingToSetting = onFinishedScrollingToSetting,
                modifier = modifier,
            )
        }
        SettingsCategory.PatternCollections -> {
            PatternCollectionsDetail(
                detailScrollState = detailScrollState,
                showAppBar = showAppBar,
                onBackButtonPressed = onBackButtonPressed,
                settingToScrollTo = settingToScrollTo,
                onFinishedScrollingToSetting = onFinishedScrollingToSetting,
                modifier = modifier,
            )
        }
    }
}

context(_: SettingUiInjectEntryPoint, _: SettingUiLocalEntryPoint)
@OptIn(ExperimentalMaterial3Api::class, ExperimentalSharedTransitionApi::class)
@Suppress("LongMethod", "LongParameterList")
@Composable
private fun StandardSettingsCategoryDetail(
    settingsCategory: SettingsCategory,
    detailScrollState: ScrollState,
    showAppBar: Boolean,
    onBackButtonPressed: () -> Unit,
    settingToScrollTo: Setting?,
    onFinishedScrollingToSetting: () -> Unit,
    modifier: Modifier = Modifier,
) {
    Surface(
        modifier = modifier,
        color = LocalBackgroundColor.current ?: MaterialTheme.colorScheme.surface,
    ) {
        Column(
            modifier = Modifier.fillMaxSize(),
        ) {
            if (showAppBar) {
                val isElevated = detailScrollState.canScrollBackward
                val elevation by animateDpAsState(targetValue = if (isElevated) 3.dp else 0.dp)

                Surface(
                    tonalElevation = elevation,
                ) {
                    Box(
                        modifier = Modifier
                            .fillMaxWidth()
                            .windowInsetsPadding(
                                WindowInsets.safeDrawing.only(
                                    WindowInsetsSides.Horizontal + WindowInsetsSides.Top,
                                ),
                            )
                            .height(64.dp),
                    ) {
                        Box(
                            modifier = Modifier.align(Alignment.CenterStart),
                        ) {
                            TooltipBox(
                                positionProvider = TooltipDefaults.rememberTooltipPositionProvider(),
                                tooltip = {
                                    PlainTooltip {
                                        Text(parameterizedStringResource(Strings.Back))
                                    }
                                },
                                state = rememberTooltipState(),
                            ) {
                                IconButton(
                                    onClick = onBackButtonPressed,
                                ) {
                                    Icon(
                                        Icons.AutoMirrored.Default.ArrowBack,
                                        contentDescription = parameterizedStringResource(Strings.Back),
                                    )
                                }
                            }
                        }

                        Text(
                            text = settingsCategory.title,
                            modifier = Modifier.align(Alignment.Center),
                            style = MaterialTheme.typography.titleLarge,
                        )
                    }
                }
            }

            Column(
                verticalArrangement = Arrangement.spacedBy(16.dp),
                modifier = Modifier
                    .then(
                        if (showAppBar) {
                            Modifier.consumeWindowInsets(
                                WindowInsets.safeDrawing.only(
                                    WindowInsetsSides.Horizontal + WindowInsetsSides.Top,
                                ),
                            )
                        } else {
                            Modifier
                        },
                    )
                    .safeDrawingPadding()
                    .verticalScroll(detailScrollState)
                    .padding(vertical = 16.dp),
            ) {
                settingsCategory.settings.forEach { setting ->
                    var layoutCoordinates: LayoutCoordinates? by remember { mutableStateOf(null) }

                    SettingUi(
                        setting = setting,
                        modifier = Modifier
                            .padding(horizontal = 16.dp)
                            .onPlaced {
                                layoutCoordinates = it
                            }
                            .trySharedBounds(
                                key = "SettingUi-$setting",
                                resizeMode = SharedTransitionScope.ResizeMode.RemeasureToBounds,
                            ),
                    )

                    val currentOnFinishedScrollingToSetting by rememberUpdatedState(onFinishedScrollingToSetting)

                    LaunchedEffect(settingToScrollTo, layoutCoordinates) {
                        val currentLayoutCoordinates = layoutCoordinates
                        if (currentLayoutCoordinates != null && settingToScrollTo == setting) {
                            detailScrollState.animateScrollTo(
                                currentLayoutCoordinates.boundsInParent().top.roundToInt(),
                            )
                            currentOnFinishedScrollingToSetting()
                        }
                    }
                }
            }
        }
    }
}

context(injectEntryPoint: SettingUiInjectEntryPoint, _: SettingUiLocalEntryPoint)
@OptIn(ExperimentalMaterial3Api::class, ExperimentalSharedTransitionApi::class)
@Suppress("LongMethod", "LongParameterList")
@Composable
private fun PatternCollectionsDetail(
    detailScrollState: ScrollState,
    showAppBar: Boolean,
    onBackButtonPressed: () -> Unit,
    settingToScrollTo: Setting?,
    onFinishedScrollingToSetting: () -> Unit,
    modifier: Modifier = Modifier,
) {
    Surface(
        modifier = modifier,
        color = LocalBackgroundColor.current ?: MaterialTheme.colorScheme.surface,
    ) {
        Column(
            modifier = Modifier.fillMaxSize(),
        ) {
            if (showAppBar) {
                val isElevated = detailScrollState.canScrollBackward
                val elevation by animateDpAsState(targetValue = if (isElevated) 3.dp else 0.dp)

                Surface(
                    tonalElevation = elevation,
                ) {
                    Box(
                        modifier = Modifier
                            .fillMaxWidth()
                            .windowInsetsPadding(
                                WindowInsets.safeDrawing.only(
                                    WindowInsetsSides.Horizontal + WindowInsetsSides.Top,
                                ),
                            )
                            .height(64.dp),
                    ) {
                        Box(
                            modifier = Modifier.align(Alignment.CenterStart),
                        ) {
                            TooltipBox(
                                positionProvider = TooltipDefaults.rememberTooltipPositionProvider(),
                                tooltip = {
                                    PlainTooltip {
                                        Text(parameterizedStringResource(Strings.Back))
                                    }
                                },
                                state = rememberTooltipState(),
                            ) {
                                IconButton(
                                    onClick = onBackButtonPressed,
                                ) {
                                    Icon(
                                        Icons.AutoMirrored.Default.ArrowBack,
                                        contentDescription = parameterizedStringResource(Strings.Back),
                                    )
                                }
                            }
                        }

                        Text(
                            text = SettingsCategory.PatternCollections.title,
                            modifier = Modifier.align(Alignment.Center),
                            style = MaterialTheme.typography.titleLarge,
                        )
                    }
                }
            }

            var isRefreshing by remember { mutableStateOf(false) }
            val coroutineScope = rememberCoroutineScope()

            PullToRefreshBox(
                isRefreshing = isRefreshing,
                onRefresh = {
                    coroutineScope.launch {
                        isRefreshing = true
                        try {
                            injectEntryPoint.patternCollectionRepository.synchronizePatternCollections()
                        } finally {
                            isRefreshing = false
                        }
                    }
                },
            ) {
                Column(
                    verticalArrangement = Arrangement.spacedBy(16.dp),
                    modifier = Modifier
                        .fillMaxSize()
                        .then(
                            if (showAppBar) {
                                Modifier.consumeWindowInsets(
                                    WindowInsets.safeDrawing.only(
                                        WindowInsetsSides.Horizontal + WindowInsetsSides.Top,
                                    ),
                                )
                            } else {
                                Modifier
                            },
                        )
                        .safeDrawingPadding()
                        .verticalScroll(detailScrollState)
                        .padding(vertical = 16.dp),
                ) {
                    SettingsCategory.PatternCollections.settings.forEach { setting ->
                        var layoutCoordinates: LayoutCoordinates? by remember { mutableStateOf(null) }

                        SettingUi(
                            setting = setting,
                            modifier = Modifier
                                .padding(horizontal = 16.dp)
                                .onPlaced {
                                    layoutCoordinates = it
                                }
                                .trySharedBounds(
                                    key = "SettingUi-$setting",
                                    resizeMode = SharedTransitionScope.ResizeMode.RemeasureToBounds,
                                ),
                        )

                        val currentOnFinishedScrollingToSetting by rememberUpdatedState(onFinishedScrollingToSetting)

                        LaunchedEffect(settingToScrollTo, layoutCoordinates) {
                            val currentLayoutCoordinates = layoutCoordinates
                            if (currentLayoutCoordinates != null && settingToScrollTo == setting) {
                                detailScrollState.animateScrollTo(
                                    currentLayoutCoordinates.boundsInParent().top.roundToInt(),
                                )
                                currentOnFinishedScrollingToSetting()
                            }
                        }
                    }
                }
            }
        }
    }
}

interface FullscreenSettingsDetailPaneState : ListDetailInfo {
    val settingsCategory: SettingsCategory

    /**
     * If non-null, a [Setting] to scroll to immediately.
     */
    val settingToScrollTo: Setting?

    /**
     * A callback that [settingToScrollTo] has been scrolled to, and shouldn't be scrolled to again.
     */
    fun onFinishedScrollingToSetting()
}
