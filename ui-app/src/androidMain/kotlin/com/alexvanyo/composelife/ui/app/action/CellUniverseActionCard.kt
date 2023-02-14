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
import androidx.compose.animation.core.spring
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.layout.widthIn
import androidx.compose.foundation.layout.wrapContentSize
import androidx.compose.foundation.rememberScrollState
import androidx.compose.foundation.shape.RoundedCornerShape
import androidx.compose.material3.Card
import androidx.compose.material3.CardDefaults
import androidx.compose.material3.MaterialTheme
import androidx.compose.material3.windowsizeclass.WindowSizeClass
import androidx.compose.runtime.Composable
import androidx.compose.runtime.key
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.Shape
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.model.TemporalGameOfLifeState
import com.alexvanyo.composelife.ui.app.action.settings.FullscreenSettingsScreen
import com.alexvanyo.composelife.ui.app.action.settings.FullscreenSettingsScreenHiltEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.FullscreenSettingsScreenLocalEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.InlineSettingsScreen
import com.alexvanyo.composelife.ui.app.action.settings.InlineSettingsScreenHiltEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.InlineSettingsScreenLocalEntryPoint
import com.alexvanyo.composelife.ui.util.AnimatedContent
import com.alexvanyo.composelife.ui.util.PredictiveNavigationHost
import com.alexvanyo.composelife.ui.util.isInProgress
import com.livefront.sealedenum.GenSealedEnum
import dagger.hilt.EntryPoint
import dagger.hilt.InstallIn
import dagger.hilt.android.components.ActivityComponent
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.launch

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
    shape: Shape = RoundedCornerShape(12.0.dp),
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
        shape = shape,
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
    shape: Shape = RoundedCornerShape(12.0.dp),
) {
    Card(
        shape = shape,
        colors = CardDefaults.cardColors(
            containerColor = MaterialTheme.colorScheme.surface,
        ),
        elevation = CardDefaults.cardElevation(
            defaultElevation = 1.dp,
        ),
        modifier = modifier,
    ) {
        val contentScrollStateMap =
            actionCardState.navigationState.entryMap.mapValues { (entryId, _) ->
                key(entryId) {
                    rememberScrollState()
                }
            }

        val currentScrollState = contentScrollStateMap.getValue(
            actionCardState.navigationState.currentEntryId,
        )

        Column(
            horizontalAlignment = Alignment.CenterHorizontally,
        ) {
            AnimatedContent(
                targetState = actionCardState.fullscreenTargetState,
                contentAlignment = Alignment.BottomCenter,
            ) { isFullscreen ->
                Box(
                    modifier = Modifier.widthIn(max = 480.dp).wrapContentSize(),
                ) {
                    if (isFullscreen) {
                        Spacer(modifier = Modifier.fillMaxWidth())
                    } else {
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
                }
            }

            AnimatedContent(
                targetState = actionCardState.expandedTargetState,
                contentAlignment = Alignment.BottomCenter,
                contentSizeAnimationSpec = spring(
                    stiffness = Spring.StiffnessMedium,
                ),
            ) { isExpanded ->
                if (isExpanded) {
                    Column(
                        horizontalAlignment = Alignment.CenterHorizontally,
                    ) {
                        PredictiveNavigationHost(
                            predictiveBackState = actionCardState.predictiveBackState,
                            backstackState = actionCardState.navigationState,
                            modifier = Modifier.weight(1f, fill = false),
                            contentAlignment = Alignment.BottomCenter,
                        ) { entry ->
                            // Cache the scroll state based for the target entry id.
                            // This value won't change normally, but it will ensure we keep using the old state
                            // while being removed from the backstack
                            val scrollState = remember { contentScrollStateMap.getValue(entry.id) }

                            Box(
                                modifier = if (entry.value.isFullscreen) {
                                    Modifier
                                } else {
                                    Modifier.widthIn(max = 480.dp)
                                }
                            ) {
                                when (val value = entry.value) {
                                    is ActionCardNavigation.Speed -> {
                                        when (value) {
                                            ActionCardNavigation.Speed.Inline -> {
                                                InlineSpeedScreen(
                                                    targetStepsPerSecond = targetStepsPerSecond,
                                                    setTargetStepsPerSecond = setTargetStepsPerSecond,
                                                    generationsPerStep = generationsPerStep,
                                                    setGenerationsPerStep = setGenerationsPerStep,
                                                    scrollState = scrollState,
                                                    modifier = Modifier.fillMaxWidth(),
                                                )
                                            }
                                        }
                                    }

                                    is ActionCardNavigation.Edit -> {
                                        when (value) {
                                            ActionCardNavigation.Edit.Inline -> {
                                                InlineEditScreen(modifier = Modifier.fillMaxWidth())
                                            }
                                        }
                                    }

                                    is ActionCardNavigation.Settings -> {
                                        when (value) {
                                            ActionCardNavigation.Settings.Inline -> {
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

                                            is ActionCardNavigation.Settings.Fullscreen -> {
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

                        AnimatedContent(
                            targetState = actionCardState.fullscreenTargetState,
                            contentAlignment = Alignment.BottomCenter,
                        ) { isFullscreen ->
                            Box(
                                modifier = Modifier.widthIn(max = 480.dp),
                            ) {
                                if (isFullscreen) {
                                    Spacer(modifier = Modifier.fillMaxWidth())
                                } else {
                                    ActionCardNavigationBar(
                                        actionCardState = actionCardState,
                                        isElevated = currentScrollState.canScrollForward,
                                    )
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}

internal sealed interface ActionCardDestinationLayoutTypes {
    object BottomBar : ActionCardDestinationLayoutTypes
    object NavHost : ActionCardDestinationLayoutTypes

    @GenSealedEnum
    companion object
}
