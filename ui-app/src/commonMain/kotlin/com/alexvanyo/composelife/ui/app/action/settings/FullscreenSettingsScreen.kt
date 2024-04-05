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

import androidx.compose.animation.core.animateDpAsState
import androidx.compose.foundation.ScrollState
import androidx.compose.foundation.layout.Arrangement
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.Row
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
import androidx.compose.foundation.layout.sizeIn
import androidx.compose.foundation.layout.windowInsetsPadding
import androidx.compose.foundation.rememberScrollState
import androidx.compose.foundation.shape.RoundedCornerShape
import androidx.compose.foundation.verticalScroll
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.automirrored.filled.ArrowBack
import androidx.compose.material.icons.filled.Analytics
import androidx.compose.material.icons.filled.Flag
import androidx.compose.material.icons.filled.Palette
import androidx.compose.material.icons.outlined.Analytics
import androidx.compose.material.icons.outlined.Flag
import androidx.compose.material.icons.outlined.Palette
import androidx.compose.material3.Card
import androidx.compose.material3.CardDefaults
import androidx.compose.material3.ExperimentalMaterial3Api
import androidx.compose.material3.Icon
import androidx.compose.material3.IconButton
import androidx.compose.material3.MaterialTheme
import androidx.compose.material3.PlainTooltip
import androidx.compose.material3.Scaffold
import androidx.compose.material3.Surface
import androidx.compose.material3.Text
import androidx.compose.material3.TooltipBox
import androidx.compose.material3.TooltipDefaults
import androidx.compose.material3.rememberTooltipState
import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.runtime.setValue
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.vector.ImageVector
import androidx.compose.ui.layout.LayoutCoordinates
import androidx.compose.ui.layout.boundsInParent
import androidx.compose.ui.layout.onPlaced
import androidx.compose.ui.semantics.selected
import androidx.compose.ui.semantics.semantics
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResource
import com.alexvanyo.composelife.ui.app.ComposeLifeUiNavigation
import com.alexvanyo.composelife.ui.app.resources.Algorithm
import com.alexvanyo.composelife.ui.app.resources.Back
import com.alexvanyo.composelife.ui.app.resources.FeatureFlags
import com.alexvanyo.composelife.ui.app.resources.Settings
import com.alexvanyo.composelife.ui.app.resources.Strings
import com.alexvanyo.composelife.ui.app.resources.Visual
import kotlin.math.roundToInt

interface FullscreenSettingsPaneInjectEntryPoint :
    SettingUiInjectEntryPoint

interface FullscreenSettingsPaneLocalEntryPoint :
    SettingUiLocalEntryPoint

@Composable
fun FullscreenSettingsListPane(
    navEntryValue: ComposeLifeUiNavigation.FullscreenSettingsList,
    setSettingsCategory: (SettingsCategory) -> Unit,
    onBackButtonPressed: () -> Unit,
    modifier: Modifier = Modifier,
) {
    SettingsCategoryList(
        currentSettingsCategory = navEntryValue.nav.settingsCategory,
        showSelectedSettingsCategory = navEntryValue.isDetailVisible && navEntryValue.isListVisible,
        listScrollState = rememberScrollState(),
        setSettingsCategory = setSettingsCategory,
        showFloatingAppBar = navEntryValue.isDetailVisible && navEntryValue.isListVisible,
        onBackButtonPressed = onBackButtonPressed,
        modifier = modifier,
    )
}

@OptIn(ExperimentalMaterial3Api::class)
@Suppress("LongMethod", "LongParameterList")
@Composable
private fun SettingsCategoryList(
    currentSettingsCategory: SettingsCategory,
    showSelectedSettingsCategory: Boolean,
    listScrollState: ScrollState,
    setSettingsCategory: (SettingsCategory) -> Unit,
    showFloatingAppBar: Boolean,
    onBackButtonPressed: () -> Unit,
    modifier: Modifier = Modifier,
) {
    Scaffold(
        topBar = {
            val isElevated = listScrollState.canScrollBackward
            val elevation by animateDpAsState(targetValue = if (isElevated) 3.dp else 0.dp)

            Surface(
                tonalElevation = elevation,
                shape = RoundedCornerShape(if (showFloatingAppBar) 16.dp else 0.dp),
                modifier = Modifier
                    .then(
                        if (showFloatingAppBar) {
                            Modifier
                                .windowInsetsPadding(
                                    WindowInsets.safeDrawing.only(
                                        WindowInsetsSides.Horizontal + WindowInsetsSides.Top,
                                    ),
                                )
                                .padding(4.dp)
                        } else {
                            Modifier
                        },
                    ),
            ) {
                Box(
                    modifier = Modifier
                        .fillMaxWidth()
                        .then(
                            if (showFloatingAppBar) {
                                Modifier
                            } else {
                                Modifier.windowInsetsPadding(
                                    WindowInsets.safeDrawing.only(
                                        WindowInsetsSides.Horizontal + WindowInsetsSides.Top,
                                    ),
                                )
                            },
                        )
                        .height(64.dp),
                ) {
                    Box(
                        modifier = Modifier.align(Alignment.CenterStart),
                    ) {
                        TooltipBox(
                            positionProvider = TooltipDefaults.rememberPlainTooltipPositionProvider(),
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
                                    Icons.AutoMirrored.Filled.ArrowBack,
                                    contentDescription = parameterizedStringResource(Strings.Back),
                                )
                            }
                        }
                    }

                    Text(
                        parameterizedStringResource(Strings.Settings),
                        modifier = Modifier.align(Alignment.Center),
                        style = MaterialTheme.typography.titleLarge,
                    )
                }
            }
        },
        modifier = modifier,
    ) { innerPadding ->
        Column(
            modifier = Modifier
                .fillMaxSize()
                .verticalScroll(listScrollState)
                .padding(innerPadding)
                .consumeWindowInsets(innerPadding)
                .padding(horizontal = 8.dp)
                .safeDrawingPadding(),
            verticalArrangement = Arrangement.spacedBy(16.dp),
            horizontalAlignment = Alignment.CenterHorizontally,
        ) {
            SettingsCategory.values.forEach { settingsCategory ->
                SettingsCategoryButton(
                    settingsCategory = settingsCategory,
                    showSelectedSettingsCategory = showSelectedSettingsCategory,
                    isCurrentSettingsCategory = settingsCategory == currentSettingsCategory,
                    onClick = { setSettingsCategory(settingsCategory) },
                )
            }
        }
    }
}

@Composable
private fun SettingsCategoryButton(
    settingsCategory: SettingsCategory,
    showSelectedSettingsCategory: Boolean,
    isCurrentSettingsCategory: Boolean,
    onClick: () -> Unit,
) {
    val title = settingsCategory.title
    val outlinedIcon = settingsCategory.outlinedIcon
    val filledIcon = settingsCategory.filledIcon

    val isVisuallySelected = showSelectedSettingsCategory && isCurrentSettingsCategory
    val icon = if (isVisuallySelected) filledIcon else outlinedIcon

    Card(
        colors = CardDefaults.cardColors(
            containerColor = if (isVisuallySelected) {
                MaterialTheme.colorScheme.surfaceVariant
            } else {
                MaterialTheme.colorScheme.surface
            },
        ),
        onClick = onClick,
        modifier = Modifier.semantics {
            if (showSelectedSettingsCategory) {
                selected = isCurrentSettingsCategory
            }
        },
    ) {
        Row(
            modifier = Modifier
                .sizeIn(minHeight = 64.dp)
                .padding(16.dp),
            verticalAlignment = Alignment.CenterVertically,
            horizontalArrangement = Arrangement.spacedBy(16.dp),
        ) {
            Icon(icon, contentDescription = null)
            Text(
                text = title,
                modifier = Modifier.weight(1f),
                style = MaterialTheme.typography.titleMedium,
            )
        }
    }
}

context(SettingUiInjectEntryPoint, SettingUiLocalEntryPoint)
@Composable
fun FullscreenSettingsDetailPane(
    navEntryValue: ComposeLifeUiNavigation.FullscreenSettingsDetail,
    onBackButtonPressed: () -> Unit,
    modifier: Modifier = Modifier,
) {
    SettingsCategoryDetail(
        settingsCategory = navEntryValue.nav.settingsCategory,
        detailScrollState = rememberScrollState(),
        showAppBar = !(navEntryValue.isDetailVisible && navEntryValue.isListVisible),
        onBackButtonPressed = onBackButtonPressed,
        settingToScrollTo = navEntryValue.nav.settingToScrollTo,
        onFinishedScrollingToSetting = navEntryValue.nav::onFinishedScrollingToSetting,
        modifier = modifier,
    )
}

context(SettingUiInjectEntryPoint, SettingUiLocalEntryPoint)
@OptIn(ExperimentalMaterial3Api::class)
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
    Column(
        modifier = modifier,
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
                            positionProvider = TooltipDefaults.rememberPlainTooltipPositionProvider(),
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
                        },
                )

                val currentOnFinishedScrollingToSetting by rememberUpdatedState(onFinishedScrollingToSetting)

                LaunchedEffect(settingToScrollTo, layoutCoordinates) {
                    val currentLayoutCoordinates = layoutCoordinates
                    if (currentLayoutCoordinates != null && settingToScrollTo == setting) {
                        detailScrollState.animateScrollTo(currentLayoutCoordinates.boundsInParent().top.roundToInt())
                        currentOnFinishedScrollingToSetting()
                    }
                }
            }
        }
    }
}

private val SettingsCategory.title: String
    @Composable
    get() = when (this) {
        SettingsCategory.Algorithm -> parameterizedStringResource(Strings.Algorithm)
        SettingsCategory.FeatureFlags -> parameterizedStringResource(Strings.FeatureFlags)
        SettingsCategory.Visual -> parameterizedStringResource(Strings.Visual)
    }

private val SettingsCategory.filledIcon: ImageVector
    @Composable
    get() = when (this) {
        SettingsCategory.Algorithm -> Icons.Filled.Analytics
        SettingsCategory.FeatureFlags -> Icons.Filled.Flag
        SettingsCategory.Visual -> Icons.Filled.Palette
    }

private val SettingsCategory.outlinedIcon: ImageVector
    @Composable
    get() = when (this) {
        SettingsCategory.Algorithm -> Icons.Outlined.Analytics
        SettingsCategory.FeatureFlags -> Icons.Outlined.Flag
        SettingsCategory.Visual -> Icons.Outlined.Palette
    }
