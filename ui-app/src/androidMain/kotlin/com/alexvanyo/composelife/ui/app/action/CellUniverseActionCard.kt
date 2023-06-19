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

package com.alexvanyo.composelife.ui.app.action

import androidx.compose.animation.core.Spring
import androidx.compose.animation.core.animateDpAsState
import androidx.compose.animation.core.animateFloatAsState
import androidx.compose.animation.core.spring
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.WindowInsets
import androidx.compose.foundation.layout.add
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.layout.safeDrawing
import androidx.compose.foundation.layout.widthIn
import androidx.compose.foundation.layout.windowInsetsPadding
import androidx.compose.foundation.rememberScrollState
import androidx.compose.foundation.shape.RoundedCornerShape
import androidx.compose.material3.Surface
import androidx.compose.material3.windowsizeclass.WindowSizeClass
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.layout.layoutId
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.offset
import com.alexvanyo.composelife.model.TemporalGameOfLifeState
import com.alexvanyo.composelife.ui.app.action.CellUniverseActionCardLayoutTypes.ActionControlRow
import com.alexvanyo.composelife.ui.app.action.CellUniverseActionCardLayoutTypes.NavContainer
import com.alexvanyo.composelife.ui.app.action.settings.FullscreenSettingsScreen
import com.alexvanyo.composelife.ui.app.action.settings.FullscreenSettingsScreenHiltEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.FullscreenSettingsScreenLocalEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.InlineSettingsScreen
import com.alexvanyo.composelife.ui.app.action.settings.InlineSettingsScreenHiltEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.InlineSettingsScreenLocalEntryPoint
import com.alexvanyo.composelife.ui.util.AnimatedContent
import com.alexvanyo.composelife.ui.util.Layout
import com.alexvanyo.composelife.ui.util.PredictiveNavigationHost
import com.alexvanyo.composelife.ui.util.WindowInsets
import com.alexvanyo.composelife.ui.util.Zero
import com.alexvanyo.composelife.ui.util.isInProgress
import com.alexvanyo.composelife.ui.util.lerp
import com.alexvanyo.composelife.ui.util.progressToTrue
import com.livefront.sealedenum.GenSealedEnum
import dagger.hilt.EntryPoint
import dagger.hilt.InstallIn
import dagger.hilt.android.components.ActivityComponent
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.launch
import kotlin.math.max

@EntryPoint
@InstallIn(ActivityComponent::class)
interface CellUniverseActionCardHiltEntryPoint :
    FullscreenSettingsScreenHiltEntryPoint,
    InlineSettingsScreenHiltEntryPoint

interface CellUniverseActionCardLocalEntryPoint :
    FullscreenSettingsScreenLocalEntryPoint,
    InlineSettingsScreenLocalEntryPoint

context(CellUniverseActionCardHiltEntryPoint, CellUniverseActionCardLocalEntryPoint)
@Suppress("LongParameterList")
@Composable
fun CellUniverseActionCard(
    temporalGameOfLifeState: TemporalGameOfLifeState,
    windowSizeClass: WindowSizeClass,
    isViewportTracking: Boolean,
    setIsViewportTracking: (Boolean) -> Unit,
    actionCardState: CellUniverseActionCardState,
    modifier: Modifier = Modifier,
    coroutineScope: CoroutineScope = rememberCoroutineScope(),
) {
    CellUniverseActionCard(
        windowSizeClass = windowSizeClass,
        isRunning = when (temporalGameOfLifeState.status) {
            TemporalGameOfLifeState.EvolutionStatus.Paused -> false
            is TemporalGameOfLifeState.EvolutionStatus.Running -> true
        },
        setIsRunning = temporalGameOfLifeState::setIsRunning,
        onStep = {
            coroutineScope.launch {
                temporalGameOfLifeState.step()
            }
        },
        targetStepsPerSecond = temporalGameOfLifeState.targetStepsPerSecond,
        setTargetStepsPerSecond = { temporalGameOfLifeState.targetStepsPerSecond = it },
        generationsPerStep = temporalGameOfLifeState.generationsPerStep,
        setGenerationsPerStep = { temporalGameOfLifeState.generationsPerStep = it },
        isViewportTracking = isViewportTracking,
        setIsViewportTracking = setIsViewportTracking,
        actionCardState = actionCardState,
        modifier = modifier,
    )
}

context(CellUniverseActionCardHiltEntryPoint, CellUniverseActionCardLocalEntryPoint)
@Suppress("LongParameterList", "LongMethod", "ComplexMethod")
@Composable
fun CellUniverseActionCard(
    windowSizeClass: WindowSizeClass,
    isRunning: Boolean,
    setIsRunning: (Boolean) -> Unit,
    onStep: () -> Unit,
    targetStepsPerSecond: Double,
    setTargetStepsPerSecond: (Double) -> Unit,
    generationsPerStep: Int,
    setGenerationsPerStep: (Int) -> Unit,
    isViewportTracking: Boolean,
    setIsViewportTracking: (Boolean) -> Unit,
    actionCardState: CellUniverseActionCardState,
    modifier: Modifier = Modifier,
) {
    val progressToFullscreen = actionCardState.fullscreenTargetState.progressToTrue

    val targetWindowInsetsProgressToFullscreen by animateFloatAsState(
        progressToFullscreen,
        animationSpec = spring(stiffness = Spring.StiffnessHigh),
    )

    val targetWindowInsets = lerp(
        WindowInsets.safeDrawing.add(WindowInsets(all = 8.dp)),
        WindowInsets.Zero,
        targetWindowInsetsProgressToFullscreen,
    )

    val cornerSize by animateDpAsState(
        targetValue = androidx.compose.ui.unit.lerp(
            12.dp,
            0.dp,
            progressToFullscreen,
        ),
    )

    Box(
        modifier = modifier,
    ) {
        Surface(
            shape = RoundedCornerShape(cornerSize),
            tonalElevation = 1.dp,
            shadowElevation = 1.dp,
            modifier = Modifier
                .matchParentSize()
                .windowInsetsPadding(targetWindowInsets),
        ) {
            Spacer(Modifier.fillMaxSize())
        }

        PredictiveNavigationHost(
            predictiveBackState = actionCardState.predictiveBackState,
            backstackState = actionCardState.navigationState,
            contentAlignment = Alignment.BottomCenter,
        ) { entry ->
            when (val value = entry.value) {
                ActionCardNavigation.Inline -> {
                    val contentScrollStateMap =
                        actionCardState.inlineNavigationState.entryMap.mapValues { (entryId, _) ->
                            key(entryId) {
                                rememberScrollState()
                            }
                        }

                    val currentScrollState = contentScrollStateMap.getValue(
                        actionCardState.inlineNavigationState.currentEntryId,
                    )

                    Surface(
                        shape = RoundedCornerShape(cornerSize),
                        tonalElevation = 1.dp,
                        modifier = Modifier.windowInsetsPadding(
                            WindowInsets.safeDrawing.add(WindowInsets(all = 8.dp)),
                        ),
                    ) {
                        Layout(
                            layoutIdTypes = CellUniverseActionCardLayoutTypes.sealedEnum,
                            content = {
                                Box(
                                    modifier = Modifier
                                        .layoutId(ActionControlRow)
                                        .widthIn(max = 480.dp),
                                    propagateMinConstraints = true,
                                ) {
                                    ActionControlRow(
                                        isElevated = !actionCardState.expandedTargetState.isInProgress() &&
                                            actionCardState.expandedTargetState.current &&
                                            currentScrollState.canScrollBackward,
                                        isRunning = isRunning,
                                        setIsRunning = setIsRunning,
                                        onStep = onStep,
                                        isExpanded = actionCardState.expandedTargetState.current,
                                        setIsExpanded = actionCardState::setIsExpanded,
                                        isViewportTracking = isViewportTracking,
                                        setIsViewportTracking = setIsViewportTracking,
                                    )
                                }

                                AnimatedContent(
                                    targetState = actionCardState.expandedTargetState,
                                    contentAlignment = Alignment.BottomCenter,
                                    contentSizeAnimationSpec = spring(
                                        stiffness = Spring.StiffnessMedium,
                                    ),
                                    modifier = Modifier.layoutId(NavContainer),
                                ) { isExpanded ->
                                    if (isExpanded) {
                                        Column(
                                            horizontalAlignment = Alignment.CenterHorizontally,
                                        ) {
                                            PredictiveNavigationHost(
                                                predictiveBackState = actionCardState.inlinePredictiveBackState,
                                                backstackState = actionCardState.inlineNavigationState,
                                                modifier = Modifier.weight(1f, fill = false),
                                                contentAlignment = Alignment.BottomCenter,
                                            ) { entry ->
                                                // Cache the scroll state based for the target entry id.
                                                // This value won't change normally, but it will ensure we keep using
                                                // the old state while being removed from the backstack
                                                val scrollState =
                                                    remember { contentScrollStateMap.getValue(entry.id) }

                                                Box(
                                                    Modifier.widthIn(max = 480.dp),
                                                ) {
                                                    when (entry.value) {
                                                        is InlineActionCardNavigation.Speed -> {
                                                            InlineSpeedScreen(
                                                                targetStepsPerSecond = targetStepsPerSecond,
                                                                setTargetStepsPerSecond = setTargetStepsPerSecond,
                                                                generationsPerStep = generationsPerStep,
                                                                setGenerationsPerStep = setGenerationsPerStep,
                                                                scrollState = scrollState,
                                                                modifier = Modifier.fillMaxWidth(),
                                                            )
                                                        }

                                                        is InlineActionCardNavigation.Edit -> {
                                                            InlineEditScreen(
                                                                modifier = Modifier.fillMaxWidth(),
                                                                scrollState = scrollState,
                                                            )
                                                        }

                                                        is InlineActionCardNavigation.Settings -> {
                                                            InlineSettingsScreen(
                                                                onSeeMoreClicked = {
                                                                    actionCardState.onSeeMoreSettingsClicked(
                                                                        actorBackstackEntryId = entry.id,
                                                                    )
                                                                },
                                                                onOpenInSettingsClicked = { setting ->
                                                                    actionCardState.onOpenInSettingsClicked(
                                                                        setting = setting,
                                                                        actorBackstackEntryId = entry.id,
                                                                    )
                                                                },
                                                                modifier = Modifier.fillMaxWidth(),
                                                                scrollState = scrollState,
                                                            )
                                                        }
                                                    }
                                                }
                                            }

                                            Box(
                                                modifier = Modifier.widthIn(max = 480.dp),
                                            ) {
                                                ActionCardNavigationBar(
                                                    actionCardState = actionCardState,
                                                    isElevated = currentScrollState.canScrollForward,
                                                )
                                            }
                                        }
                                    }
                                }
                            },
                            measurePolicy = { measurables, constraints ->
                                val actionControlRowMeasurable = measurables.getValue(ActionControlRow)
                                val navContainerMeasurable = measurables.getValue(NavContainer)

                                // Measure the nav container after removing the height that the action control row will
                                // take up
                                val navContainerPlaceable = navContainerMeasurable.measure(
                                    constraints.offset(
                                        vertical = -actionControlRowMeasurable.minIntrinsicHeight(constraints.maxWidth),
                                    ),
                                )
                                // Measure the action control row to at least as big as the nav container
                                val actionControlRowPlaceable = actionControlRowMeasurable.measure(
                                    constraints.copy(minWidth = navContainerPlaceable.width),
                                )

                                val width = max(actionControlRowPlaceable.width, navContainerPlaceable.width)

                                layout(
                                    width = width,
                                    height = actionControlRowPlaceable.height + navContainerPlaceable.height,
                                ) {
                                    actionControlRowPlaceable.placeRelative(0, 0)
                                    navContainerPlaceable.placeRelative(
                                        (width - navContainerPlaceable.width) / 2,
                                        actionControlRowPlaceable.height,
                                    )
                                }
                            },
                        )
                    }
                }

                is ActionCardNavigation.FullscreenSettings -> {
                    Surface(
                        shape = RoundedCornerShape(cornerSize),
                        tonalElevation = 1.dp,
                    ) {
                        FullscreenSettingsScreen(
                            windowSizeClass = windowSizeClass,
                            fullscreen = value,
                            onBackButtonPressed = {
                                actionCardState.onBackPressed(
                                    actorBackstackEntryId = entry.id,
                                )
                            },
                            modifier = Modifier.fillMaxWidth(),
                        )
                    }
                }
            }
        }
    }
}

internal sealed interface CellUniverseActionCardLayoutTypes {
    object ActionControlRow : CellUniverseActionCardLayoutTypes
    object NavContainer : CellUniverseActionCardLayoutTypes

    @GenSealedEnum
    companion object
}
