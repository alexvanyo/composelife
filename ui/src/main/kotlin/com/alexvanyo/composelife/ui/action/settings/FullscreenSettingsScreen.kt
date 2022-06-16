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

package com.alexvanyo.composelife.ui.action.settings

import androidx.activity.compose.BackHandler
import androidx.compose.animation.AnimatedContent
import androidx.compose.animation.ExperimentalAnimationApi
import androidx.compose.animation.core.animateDpAsState
import androidx.compose.animation.core.tween
import androidx.compose.animation.fadeIn
import androidx.compose.animation.fadeOut
import androidx.compose.animation.with
import androidx.compose.foundation.ScrollState
import androidx.compose.foundation.layout.Arrangement
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.BoxWithConstraints
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.ExperimentalLayoutApi
import androidx.compose.foundation.layout.Row
import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.WindowInsets
import androidx.compose.foundation.layout.WindowInsetsSides
import androidx.compose.foundation.layout.consumedWindowInsets
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
import androidx.compose.material.icons.filled.Analytics
import androidx.compose.material.icons.filled.ArrowBack
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
import androidx.compose.material3.Scaffold
import androidx.compose.material3.Surface
import androidx.compose.material3.Text
import androidx.compose.material3.windowsizeclass.ExperimentalMaterial3WindowSizeClassApi
import androidx.compose.material3.windowsizeclass.WindowSizeClass
import androidx.compose.material3.windowsizeclass.WindowWidthSizeClass
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.movableContentOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.vector.ImageVector
import androidx.compose.ui.res.stringResource
import androidx.compose.ui.semantics.selected
import androidx.compose.ui.semantics.semantics
import androidx.compose.ui.unit.DpSize
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.ui.R
import com.alexvanyo.composelife.ui.action.ActionCardNavigation
import com.alexvanyo.composelife.ui.theme.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.SizePreviews
import com.alexvanyo.composelife.ui.util.canScrollUp

@Suppress("LongMethod")
@OptIn(ExperimentalLayoutApi::class, ExperimentalAnimationApi::class)
@Composable
fun FullscreenSettingsScreen(
    windowSizeClass: WindowSizeClass,
    fullscreen: ActionCardNavigation.Settings.Fullscreen,
    onBackButtonPressed: () -> Unit,
    modifier: Modifier = Modifier,
) {
    val currentWindowSizeClass by rememberUpdatedState(windowSizeClass)

    val listScrollState = rememberScrollState()
    val detailScrollStates = SettingsCategory.values.associateWith {
        key(it) { rememberScrollState() }
    }

    fun showList() =
        when (currentWindowSizeClass.widthSizeClass) {
            WindowWidthSizeClass.Compact -> !fullscreen.showDetails
            else -> true
        }

    fun showDetail() =
        when (currentWindowSizeClass.widthSizeClass) {
            WindowWidthSizeClass.Compact -> fullscreen.showDetails
            else -> true
        }

    fun showListAndDetail() = showList() && showDetail()

    if (showDetail() && !showList()) {
        BackHandler {
            fullscreen.showDetails = false
        }
    }

    val listContent = remember(fullscreen) {
        movableContentOf {
            SettingsCategoryList(
                currentSettingsCategory = fullscreen.settingsCategory,
                showSelectedSettingsCategory = showListAndDetail(),
                listScrollState = listScrollState,
                setSettingsCategory = {
                    fullscreen.settingsCategory = it
                    fullscreen.showDetails = true
                },
                showFloatingAppBar = showListAndDetail(),
                onBackButtonPressed = onBackButtonPressed,
            )
        }
    }

    val detailContent = remember(fullscreen) {
        movableContentOf { settingsCategory: SettingsCategory ->
            val detailScrollState = detailScrollStates.getValue(settingsCategory)

            SettingsCategoryDetail(
                settingsCategory = settingsCategory,
                detailScrollState = detailScrollState,
                showAppBar = !showListAndDetail(),
                onBackButtonPressed = { fullscreen.showDetails = false },
            )
        }
    }

    if (showListAndDetail()) {
        Row(modifier = modifier) {
            Box(
                modifier = Modifier
                    .weight(1f)
                    .consumedWindowInsets(WindowInsets.safeDrawing.only(WindowInsetsSides.End)),
            ) {
                listContent()
            }

            Surface(
                color = MaterialTheme.colorScheme.secondaryContainer,
                shape = RoundedCornerShape(16.dp),
                modifier = Modifier
                    .weight(1f)
                    .consumedWindowInsets(WindowInsets.safeDrawing.only(WindowInsetsSides.Start))
                    .safeDrawingPadding()
                    .padding(
                        top = 4.dp,
                        start = 8.dp,
                        end = 8.dp,
                        bottom = 16.dp,
                    ),
            ) {
                AnimatedContent(
                    targetState = fullscreen.settingsCategory,
                    transitionSpec = {
                        fadeIn(animationSpec = tween(220, delayMillis = 90)) with
                            fadeOut(animationSpec = tween(90))
                    },
                ) { settingsCategory ->
                    detailContent(settingsCategory)
                }
            }
        }
    } else {
        Box(modifier = modifier) {
            AnimatedContent(
                targetState = showList(),
                transitionSpec = {
                    fadeIn(animationSpec = tween(220, delayMillis = 90)) with
                        fadeOut(animationSpec = tween(90))
                },
            ) { showList ->
                if (showList) {
                    listContent()
                } else {
                    detailContent(fullscreen.settingsCategory)
                }
            }
        }
    }
}

@OptIn(ExperimentalMaterial3Api::class, ExperimentalLayoutApi::class)
@Suppress("LongMethod", "LongParameterList")
@Composable
private fun SettingsCategoryList(
    currentSettingsCategory: SettingsCategory,
    showSelectedSettingsCategory: Boolean,
    listScrollState: ScrollState,
    setSettingsCategory: (SettingsCategory) -> Unit,
    showFloatingAppBar: Boolean,
    onBackButtonPressed: () -> Unit,
) {
    Scaffold(
        topBar = {
            val isElevated = listScrollState.canScrollUp
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
                    IconButton(
                        onClick = onBackButtonPressed,
                        modifier = Modifier.align(Alignment.CenterStart),
                    ) {
                        Icon(
                            Icons.Default.ArrowBack,
                            contentDescription = stringResource(id = R.string.back),
                        )
                    }

                    Text(
                        stringResource(id = R.string.settings),
                        modifier = Modifier.align(Alignment.Center),
                        style = MaterialTheme.typography.titleLarge,
                    )
                }
            }
        },
    ) { innerPadding ->
        Column(
            modifier = Modifier
                .fillMaxSize()
                .verticalScroll(listScrollState)
                .padding(innerPadding)
                .consumedWindowInsets(innerPadding)
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
@OptIn(ExperimentalMaterial3Api::class)
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

@Composable
private fun SettingsCategoryDetail(
    settingsCategory: SettingsCategory,
    detailScrollState: ScrollState,
    showAppBar: Boolean,
    onBackButtonPressed: () -> Unit,
) {
    Column(
        modifier = Modifier
            .fillMaxSize()
            .verticalScroll(detailScrollState),
    ) {
        if (showAppBar) {
            val isElevated = detailScrollState.canScrollUp
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
                    IconButton(
                        onClick = onBackButtonPressed,
                        modifier = Modifier.align(Alignment.CenterStart),
                    ) {
                        Icon(
                            Icons.Default.ArrowBack,
                            contentDescription = stringResource(id = R.string.back),
                        )
                    }

                    Text(
                        text = settingsCategory.title,
                        modifier = Modifier.align(Alignment.Center),
                        style = MaterialTheme.typography.titleLarge,
                    )
                }
            }
        }

        Spacer(modifier = Modifier.height(16.dp))

        Column(
            verticalArrangement = Arrangement.spacedBy(16.dp),
        ) {
            settingsCategory.settings.forEach { setting ->
                SettingUi(
                    setting = setting,
                    modifier = Modifier.padding(horizontal = 16.dp),
                )
            }
        }
    }
}

private val SettingsCategory.title: String
    @Composable
    get() = when (this) {
        SettingsCategory.Algorithm -> stringResource(id = R.string.algorithm)
        SettingsCategory.FeatureFlags -> stringResource(id = R.string.feature_flags)
        SettingsCategory.Visual -> stringResource(id = R.string.visual)
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

@OptIn(ExperimentalMaterial3WindowSizeClassApi::class)
@SizePreviews
@Composable
fun FullscreenSettingsScreenListPreview() {
    ComposeLifeTheme {
        BoxWithConstraints {
            val size = DpSize(maxWidth, maxHeight)
            Surface {
                FullscreenSettingsScreen(
                    windowSizeClass = WindowSizeClass.calculateFromSize(size),
                    fullscreen = ActionCardNavigation.Settings.Fullscreen(
                        initialSettingsCategory = SettingsCategory.Algorithm,
                        initialShowDetails = false,
                    ),
                    onBackButtonPressed = {},
                    modifier = Modifier.fillMaxSize(),
                )
            }
        }
    }
}

@OptIn(ExperimentalMaterial3WindowSizeClassApi::class)
@SizePreviews
@Composable
fun FullscreenSettingsScreenDetailsPreview() {
    ComposeLifeTheme {
        BoxWithConstraints {
            val size = DpSize(maxWidth, maxHeight)
            Surface {
                FullscreenSettingsScreen(
                    windowSizeClass = WindowSizeClass.calculateFromSize(size),
                    fullscreen = ActionCardNavigation.Settings.Fullscreen(
                        initialSettingsCategory = SettingsCategory.Algorithm,
                        initialShowDetails = true,
                    ),
                    onBackButtonPressed = {},
                    modifier = Modifier.fillMaxSize(),
                )
            }
        }
    }
}
