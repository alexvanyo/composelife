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

package com.alexvanyo.composelife.ui.action

import androidx.activity.compose.BackHandler
import androidx.compose.animation.AnimatedContent
import androidx.compose.animation.AnimatedVisibility
import androidx.compose.animation.ExperimentalAnimationApi
import androidx.compose.animation.core.tween
import androidx.compose.animation.expandIn
import androidx.compose.animation.fadeIn
import androidx.compose.animation.fadeOut
import androidx.compose.animation.shrinkOut
import androidx.compose.animation.with
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.layout.height
import androidx.compose.foundation.rememberScrollState
import androidx.compose.foundation.shape.RoundedCornerShape
import androidx.compose.material3.Card
import androidx.compose.material3.CardDefaults
import androidx.compose.material3.ExperimentalMaterial3Api
import androidx.compose.material3.MaterialTheme
import androidx.compose.material3.windowsizeclass.WindowSizeClass
import androidx.compose.runtime.Composable
import androidx.compose.runtime.key
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.Shape
import androidx.compose.ui.unit.IntSize
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.model.TemporalGameOfLifeState
import com.alexvanyo.composelife.navigation.NavigationHost
import com.alexvanyo.composelife.ui.action.settings.FullscreenSettingsScreen
import com.alexvanyo.composelife.ui.action.settings.InlineSettingsScreen
import com.alexvanyo.composelife.ui.util.canScrollDown
import com.alexvanyo.composelife.ui.util.canScrollUp
import com.livefront.sealedenum.GenSealedEnum
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.launch

@Suppress("LongParameterList")
@Composable
fun CellUniverseActionCard(
    temporalGameOfLifeState: TemporalGameOfLifeState,
    windowSizeClass: WindowSizeClass,
    isTopCard: Boolean,
    modifier: Modifier = Modifier,
    shape: Shape = RoundedCornerShape(12.0.dp),
    actionCardState: CellUniverseActionCardState = rememberCellUniverseActionCardState(),
    coroutineScope: CoroutineScope = rememberCoroutineScope(),
) {
    CellUniverseActionCard(
        windowSizeClass = windowSizeClass,
        isTopCard = isTopCard,
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
        shape = shape,
        actionCardState = actionCardState,
        modifier = modifier,
    )
}

@Suppress("LongParameterList", "LongMethod", "ComplexMethod")
@OptIn(ExperimentalMaterial3Api::class, ExperimentalAnimationApi::class)
@Composable
fun CellUniverseActionCard(
    windowSizeClass: WindowSizeClass,
    isTopCard: Boolean,
    isRunning: Boolean,
    setIsRunning: (Boolean) -> Unit,
    onStep: () -> Unit,
    targetStepsPerSecond: Double,
    setTargetStepsPerSecond: (Double) -> Unit,
    generationsPerStep: Int,
    setGenerationsPerStep: (Int) -> Unit,
    modifier: Modifier = Modifier,
    shape: Shape = RoundedCornerShape(12.0.dp),
    actionCardState: CellUniverseActionCardState = rememberCellUniverseActionCardState(),
) {
    if (actionCardState.isExpanded && actionCardState.canNavigateBack) {
        BackHandler(enabled = isTopCard) {
            actionCardState.onBackPressed(actionCardState.navigationState.currentEntryId)
        }
    }

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
            if (actionCardState.isExpanded && actionCardState.canNavigateBack) {
                BackHandler(enabled = isTopCard) {
                    actionCardState.onBackPressed(actionCardState.navigationState.currentEntryId)
                }
            }

            AnimatedVisibility(visible = !actionCardState.isFullscreen) {
                ActionControlRow(
                    isElevated = actionCardState.isExpanded && currentScrollState.canScrollUp,
                    isRunning = isRunning,
                    setIsRunning = setIsRunning,
                    onStep = onStep,
                    isExpanded = actionCardState.isExpanded,
                    setIsExpanded = { actionCardState.isExpanded = it },
                )
            }

            AnimatedVisibility(visible = !actionCardState.isFullscreen && actionCardState.isExpanded) {
                Spacer(modifier = Modifier.height(8.dp))
            }

            AnimatedContent(
                targetState = actionCardState.isExpanded,
                transitionSpec = {
                    fadeIn(animationSpec = tween(220, delayMillis = 90)) with
                        fadeOut(animationSpec = tween(90))
                },
                contentAlignment = Alignment.BottomCenter,
            ) { isExpanded ->
                if (isExpanded) {
                    Column {
                        NavigationHost(
                            navigationState = actionCardState.navigationState,
                            transitionSpec = {
                                fadeIn(animationSpec = tween(220, delayMillis = 90)) with
                                    fadeOut(animationSpec = tween(90))
                            },
                            contentAlignment = Alignment.BottomCenter,
                            modifier = Modifier.weight(1f, fill = false),
                        ) { entry ->
                            // Cache the scroll state based for the target entry id.
                            // This value won't change normally, but it will ensure we keep using the old state
                            // while being removed from the backstack
                            val scrollState = remember { contentScrollStateMap.getValue(entry.id) }

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
                                is ActionCardNavigation.Palette -> {
                                    when (value) {
                                        ActionCardNavigation.Palette.Inline -> {
                                            InlinePaletteScreen(
                                                scrollState = scrollState,
                                                modifier = Modifier.fillMaxWidth(),
                                            )
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
                                                scrollState = scrollState,
                                                modifier = Modifier.fillMaxWidth(),
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

                        AnimatedVisibility(
                            visible = !actionCardState.isFullscreen,
                            enter = expandIn(expandFrom = Alignment.Center) { IntSize(it.width, 0) } +
                                fadeIn(animationSpec = tween(220, delayMillis = 90)),
                            exit = shrinkOut(shrinkTowards = Alignment.Center) { IntSize(it.width, 0) } +
                                fadeOut(animationSpec = tween(90)),
                        ) {
                            ActionCardNavigationBar(
                                actionCardState = actionCardState,
                                isElevated = currentScrollState.canScrollDown,
                            )
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
