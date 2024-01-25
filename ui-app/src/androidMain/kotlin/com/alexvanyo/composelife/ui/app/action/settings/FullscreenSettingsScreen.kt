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

import androidx.compose.animation.animateColorAsState
import androidx.compose.animation.core.animateDpAsState
import androidx.compose.animation.core.exponentialDecay
import androidx.compose.animation.core.spring
import androidx.compose.foundation.Canvas
import androidx.compose.foundation.ExperimentalFoundationApi
import androidx.compose.foundation.ScrollState
import androidx.compose.foundation.gestures.AnchoredDraggableState
import androidx.compose.foundation.gestures.DraggableAnchors
import androidx.compose.foundation.gestures.Orientation
import androidx.compose.foundation.gestures.anchoredDraggable
import androidx.compose.foundation.hoverable
import androidx.compose.foundation.interaction.MutableInteractionSource
import androidx.compose.foundation.interaction.collectIsDraggedAsState
import androidx.compose.foundation.interaction.collectIsHoveredAsState
import androidx.compose.foundation.interaction.collectIsPressedAsState
import androidx.compose.foundation.layout.Arrangement
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.BoxWithConstraints
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.Row
import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.WindowInsets
import androidx.compose.foundation.layout.WindowInsetsSides
import androidx.compose.foundation.layout.consumeWindowInsets
import androidx.compose.foundation.layout.fillMaxHeight
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.layout.height
import androidx.compose.foundation.layout.only
import androidx.compose.foundation.layout.padding
import androidx.compose.foundation.layout.safeDrawing
import androidx.compose.foundation.layout.safeDrawingPadding
import androidx.compose.foundation.layout.size
import androidx.compose.foundation.layout.sizeIn
import androidx.compose.foundation.layout.windowInsetsBottomHeight
import androidx.compose.foundation.layout.windowInsetsEndWidth
import androidx.compose.foundation.layout.windowInsetsPadding
import androidx.compose.foundation.layout.windowInsetsStartWidth
import androidx.compose.foundation.layout.windowInsetsTopHeight
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
import androidx.compose.material3.Scaffold
import androidx.compose.material3.Surface
import androidx.compose.material3.Text
import androidx.compose.material3.windowsizeclass.ExperimentalMaterial3WindowSizeClassApi
import androidx.compose.material3.windowsizeclass.WindowSizeClass
import androidx.compose.material3.windowsizeclass.WindowWidthSizeClass
import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.movableContentOf
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.CornerRadius
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.graphics.vector.ImageVector
import androidx.compose.ui.input.pointer.PointerIcon
import androidx.compose.ui.input.pointer.pointerHoverIcon
import androidx.compose.ui.layout.LayoutCoordinates
import androidx.compose.ui.layout.boundsInParent
import androidx.compose.ui.layout.layoutId
import androidx.compose.ui.layout.onPlaced
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.res.stringResource
import androidx.compose.ui.semantics.selected
import androidx.compose.ui.semantics.semantics
import androidx.compose.ui.unit.DpSize
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.ui.app.ComposeLifeNavigation
import com.alexvanyo.composelife.ui.app.R
import com.alexvanyo.composelife.ui.app.component.PlainTooltipBox
import com.alexvanyo.composelife.ui.app.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.app.theme.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.AnimatedContent
import com.alexvanyo.composelife.ui.util.Crossfade
import com.alexvanyo.composelife.ui.util.Layout
import com.alexvanyo.composelife.ui.util.MobileDevicePreviews
import com.alexvanyo.composelife.ui.util.RepeatablePredictiveBackHandler
import com.alexvanyo.composelife.ui.util.RepeatablePredictiveBackState
import com.alexvanyo.composelife.ui.util.TargetState
import com.alexvanyo.composelife.ui.util.rememberRepeatablePredictiveBackStateHolder
import com.livefront.sealedenum.GenSealedEnum
import kotlin.math.roundToInt

interface FullscreenSettingsScreenInjectEntryPoint :
    SettingUiInjectEntryPoint

interface FullscreenSettingsScreenLocalEntryPoint :
    SettingUiLocalEntryPoint

context(FullscreenSettingsScreenInjectEntryPoint, FullscreenSettingsScreenLocalEntryPoint)
@OptIn(ExperimentalFoundationApi::class)
@Suppress("LongMethod", "CyclomaticComplexMethod")
@Composable
fun FullscreenSettingsScreen(
    windowSizeClass: WindowSizeClass,
    navEntryValue: ComposeLifeNavigation.FullscreenSettings,
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
            WindowWidthSizeClass.Compact -> !navEntryValue.showDetails
            else -> true
        }

    fun showDetail() =
        when (currentWindowSizeClass.widthSizeClass) {
            WindowWidthSizeClass.Compact -> navEntryValue.showDetails
            else -> true
        }

    fun showListAndDetail() = showList() && showDetail()

    val predictiveBackStateHolder = rememberRepeatablePredictiveBackStateHolder()
    RepeatablePredictiveBackHandler(
        repeatablePredictiveBackStateHolder = predictiveBackStateHolder,
        enabled = showDetail() && !showList(),
    ) {
        navEntryValue.showDetails = false
    }

    val listContent = remember(navEntryValue) {
        movableContentOf {
            SettingsCategoryList(
                currentSettingsCategory = navEntryValue.settingsCategory,
                showSelectedSettingsCategory = showListAndDetail(),
                listScrollState = listScrollState,
                setSettingsCategory = {
                    navEntryValue.settingsCategory = it
                    navEntryValue.showDetails = true
                },
                showFloatingAppBar = showListAndDetail(),
                onBackButtonPressed = onBackButtonPressed,
                modifier = Modifier.fillMaxSize(),
            )
        }
    }

    val detailContent = remember(navEntryValue) {
        movableContentOf { settingsCategory: SettingsCategory ->
            val detailScrollState = detailScrollStates.getValue(settingsCategory)

            SettingsCategoryDetail(
                settingsCategory = settingsCategory,
                detailScrollState = detailScrollState,
                showAppBar = !showListAndDetail(),
                onBackButtonPressed = { navEntryValue.showDetails = false },
                settingToScrollTo = navEntryValue.settingToScrollTo,
                onFinishedScrollingToSetting = { navEntryValue.onFinishedScrollingToSetting() },
                modifier = Modifier.fillMaxSize(),
            )
        }
    }

    val density = LocalDensity.current
    val anchoredDraggableState = rememberSaveable(
        saver = AnchoredDraggableState.Saver(
            positionalThreshold = { totalDistance -> totalDistance * 0.5f },
            velocityThreshold = { with(density) { 200.dp.toPx() } },
            snapAnimationSpec = spring(),
            decayAnimationSpec = exponentialDecay(),
        ),
    ) {
        AnchoredDraggableState(
            initialValue = 0.5f,
            positionalThreshold = { totalDistance -> totalDistance * 0.5f },
            velocityThreshold = { with(density) { 200.dp.toPx() } },
            snapAnimationSpec = spring(),
            decayAnimationSpec = exponentialDecay(),
        )
    }

    val minPaneWidth = 200.dp

    if (showListAndDetail()) {
        Layout(
            layoutIdTypes = ListAndDetailLayoutTypes.sealedEnum,
            modifier = modifier,
            content = {
                Spacer(
                    modifier = Modifier
                        .layoutId(ListAndDetailLayoutTypes.StartInsets)
                        .windowInsetsStartWidth(WindowInsets.safeDrawing),
                )
                Spacer(
                    modifier = Modifier
                        .layoutId(ListAndDetailLayoutTypes.EndInsets)
                        .windowInsetsEndWidth(WindowInsets.safeDrawing),
                )

                Box(
                    modifier = Modifier
                        .layoutId(ListAndDetailLayoutTypes.List)
                        .consumeWindowInsets(WindowInsets.safeDrawing.only(WindowInsetsSides.End)),
                ) {
                    listContent()
                }

                Column(
                    Modifier
                        .layoutId(ListAndDetailLayoutTypes.Detail)
                        .consumeWindowInsets(WindowInsets.safeDrawing.only(WindowInsetsSides.Start))
                        .windowInsetsPadding(WindowInsets.safeDrawing.only(WindowInsetsSides.Horizontal))
                        .padding(
                            top = 4.dp,
                            start = 8.dp,
                            end = 8.dp,
                            bottom = 16.dp,
                        ),
                ) {
                    Spacer(Modifier.windowInsetsTopHeight(WindowInsets.safeDrawing))
                    Surface(
                        color = MaterialTheme.colorScheme.secondaryContainer,
                        shape = RoundedCornerShape(16.dp),
                        modifier = Modifier
                            .weight(1f)
                            .consumeWindowInsets(WindowInsets.safeDrawing.only(WindowInsetsSides.Vertical)),
                    ) {
                        Crossfade(
                            targetState = TargetState.Single(navEntryValue.settingsCategory),
                        ) { settingsCategory ->
                            detailContent(settingsCategory)
                        }
                    }
                    Spacer(Modifier.windowInsetsBottomHeight(WindowInsets.safeDrawing))
                }

                Box(
                    modifier = Modifier
                        .layoutId(ListAndDetailLayoutTypes.Divider)
                        .fillMaxHeight()
                        .windowInsetsPadding(WindowInsets.safeDrawing.only(WindowInsetsSides.Vertical)),
                    contentAlignment = Alignment.Center,
                ) {
                    val handleInteractionSource = remember { MutableInteractionSource() }

                    Box(
                        modifier = Modifier
                            .size(64.dp)
                            .hoverable(
                                interactionSource = handleInteractionSource,
                            )
                            .anchoredDraggable(
                                state = anchoredDraggableState,
                                orientation = Orientation.Horizontal,
                                interactionSource = handleInteractionSource,
                            )
                            .pointerHoverIcon(PointerIcon.Hand),
                        contentAlignment = Alignment.Center,
                    ) {
                        val isHandleDragged by handleInteractionSource.collectIsDraggedAsState()
                        val isHandleHovered by handleInteractionSource.collectIsHoveredAsState()
                        val isHandlePressed by handleInteractionSource.collectIsPressedAsState()
                        val isHandleActive = isHandleDragged || isHandleHovered || isHandlePressed
                        val handleWidth by animateDpAsState(
                            targetValue = if (isHandleActive) 12.dp else 4.dp,
                            label = "handleWidth",
                        )
                        val handleColor by animateColorAsState(
                            targetValue = if (isHandleActive) {
                                MaterialTheme.colorScheme.onSurface
                            } else {
                                MaterialTheme.colorScheme.outline
                            },
                            label = "handleColor",
                        )
                        Canvas(
                            modifier = Modifier.fillMaxSize(),
                        ) {
                            val handleSize = DpSize(handleWidth, 48.dp).toSize()
                            val handleOffset = Offset(
                                (size.width - handleSize.width) / 2f,
                                (size.height - handleSize.height) / 2f,
                            )
                            drawRoundRect(
                                color = handleColor,
                                topLeft = handleOffset,
                                size = handleSize,
                                cornerRadius = CornerRadius(handleSize.width / 2),
                            )
                        }
                    }
                }
            },
            measurePolicy = { measurables, constraints ->
                val startInsetsPlaceable = measurables
                    .getValue(ListAndDetailLayoutTypes.StartInsets)
                    .measure(constraints.copy(minWidth = 0))

                val endInsetsPlaceable = measurables
                    .getValue(ListAndDetailLayoutTypes.EndInsets)
                    .measure(constraints.copy(minWidth = 0))

                val minPaneWidthPx = minPaneWidth.toPx()

                val freeSpace = constraints.maxWidth -
                    startInsetsPlaceable.width -
                    endInsetsPlaceable.width -
                    minPaneWidthPx * 2

                layout(constraints.maxWidth, constraints.maxHeight) {
                    val minAnchoredDraggablePosition = 0f
                    val maxAnchoredDraggablePosition = freeSpace.coerceAtLeast(0f)

                    anchoredDraggableState.updateAnchors(
                        newAnchors = ContinuousDraggableAnchors(
                            minAnchoredDraggablePosition = minAnchoredDraggablePosition,
                            maxAnchoredDraggablePosition = maxAnchoredDraggablePosition,
                        ),
                        newTarget = anchoredDraggableState.targetValue,
                    )

                    val currentFraction = checkNotNull(
                        anchoredDraggableState.anchors.closestAnchor(
                            anchoredDraggableState.requireOffset(),
                        ),
                    )

                    val listPaneExtraSpace = freeSpace * currentFraction
                    val listPaneWidth = (startInsetsPlaceable.width + minPaneWidthPx + listPaneExtraSpace).roundToInt()
                    val detailPaneWidth = constraints.maxWidth - listPaneWidth

                    val listPanePlaceable = measurables
                        .getValue(ListAndDetailLayoutTypes.List)
                        .measure(constraints.copy(minWidth = listPaneWidth, maxWidth = listPaneWidth))

                    val detailPanePlaceable = measurables
                        .getValue(ListAndDetailLayoutTypes.Detail)
                        .measure(constraints.copy(minWidth = detailPaneWidth, maxWidth = detailPaneWidth))

                    listPanePlaceable.placeRelative(0, 0)
                    detailPanePlaceable.placeRelative(listPaneWidth, 0)

                    val dividerPlaceable = measurables
                        .getValue(ListAndDetailLayoutTypes.Divider)
                        .measure(constraints)

                    dividerPlaceable.placeRelative(listPaneWidth - dividerPlaceable.width / 2, 0)
                }
            },
        )
    } else {
        AnimatedContent(
            targetState = when (val predictiveBackState = predictiveBackStateHolder.value) {
                RepeatablePredictiveBackState.NotRunning -> TargetState.Single(showList())
                is RepeatablePredictiveBackState.Running ->
                    TargetState.InProgress(
                        current = false,
                        provisional = true,
                        progress = predictiveBackState.progress,
                    )
            },
            modifier = modifier,
        ) { showList ->
            if (showList) {
                listContent()
            } else {
                detailContent(navEntryValue.settingsCategory)
            }
        }
    }
}

@OptIn(ExperimentalFoundationApi::class)
data class ContinuousDraggableAnchors(
    private val minAnchoredDraggablePosition: Float,
    private val maxAnchoredDraggablePosition: Float,
) : DraggableAnchors<Float> {
    override val size: Int = 1

    override fun closestAnchor(position: Float): Float =
        (
            position.coerceIn(minAnchoredDraggablePosition, maxAnchoredDraggablePosition) -
                minAnchoredDraggablePosition
            ) /
            (maxAnchoredDraggablePosition - minAnchoredDraggablePosition)

    override fun closestAnchor(position: Float, searchUpwards: Boolean): Float? =
        if (searchUpwards) {
            if (position <= maxAnchoredDraggablePosition) {
                (
                    position.coerceIn(minAnchoredDraggablePosition, maxAnchoredDraggablePosition) -
                        minAnchoredDraggablePosition
                    ) /
                    (maxAnchoredDraggablePosition - minAnchoredDraggablePosition)
            } else {
                null
            }
        } else {
            if (position >= minAnchoredDraggablePosition) {
                (
                    position.coerceIn(minAnchoredDraggablePosition, maxAnchoredDraggablePosition) -
                        minAnchoredDraggablePosition
                    ) /
                    (maxAnchoredDraggablePosition - minAnchoredDraggablePosition)
            } else {
                null
            }
        }

    override fun maxAnchor(): Float = maxAnchoredDraggablePosition

    override fun minAnchor(): Float = minAnchoredDraggablePosition

    override fun positionOf(value: Float): Float =
        value * (maxAnchoredDraggablePosition - minAnchoredDraggablePosition) +
            minAnchoredDraggablePosition

    override fun hasAnchorFor(value: Float): Boolean =
        value in minAnchoredDraggablePosition..maxAnchoredDraggablePosition
}

sealed interface ListAndDetailLayoutTypes {
    data object StartInsets : ListAndDetailLayoutTypes
    data object EndInsets : ListAndDetailLayoutTypes
    data object List : ListAndDetailLayoutTypes
    data object Detail : ListAndDetailLayoutTypes
    data object Divider : ListAndDetailLayoutTypes

    @GenSealedEnum
    companion object
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
                        PlainTooltipBox(
                            tooltip = {
                                Text(stringResource(id = R.string.back))
                            },
                        ) {
                            IconButton(
                                onClick = onBackButtonPressed,
                                modifier = Modifier.tooltipAnchor(),
                            ) {
                                Icon(
                                    Icons.AutoMirrored.Filled.ArrowBack,
                                    contentDescription = stringResource(id = R.string.back),
                                )
                            }
                        }
                    }

                    Text(
                        stringResource(id = R.string.settings),
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
                        PlainTooltipBox(
                            tooltip = {
                                Text(stringResource(id = R.string.back))
                            },
                        ) {
                            IconButton(
                                onClick = onBackButtonPressed,
                                modifier = Modifier.tooltipAnchor(),
                            ) {
                                Icon(
                                    Icons.AutoMirrored.Default.ArrowBack,
                                    contentDescription = stringResource(id = R.string.back),
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
@MobileDevicePreviews
@Composable
fun FullscreenSettingsScreenListPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            BoxWithConstraints {
                val size = DpSize(maxWidth, maxHeight)
                Surface {
                    FullscreenSettingsScreen(
                        windowSizeClass = WindowSizeClass.calculateFromSize(size),
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
fun FullscreenSettingsScreenAlgorithmPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            BoxWithConstraints {
                val size = DpSize(maxWidth, maxHeight)
                Surface {
                    FullscreenSettingsScreen(
                        windowSizeClass = WindowSizeClass.calculateFromSize(size),
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
fun FullscreenSettingsScreenVisualPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            BoxWithConstraints {
                val size = DpSize(maxWidth, maxHeight)
                Surface {
                    FullscreenSettingsScreen(
                        windowSizeClass = WindowSizeClass.calculateFromSize(size),
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
fun FullscreenSettingsScreenFeatureFlagsPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            BoxWithConstraints {
                val size = DpSize(maxWidth, maxHeight)
                Surface {
                    FullscreenSettingsScreen(
                        windowSizeClass = WindowSizeClass.calculateFromSize(size),
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
