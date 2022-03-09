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
import androidx.compose.animation.animateContentSize
import androidx.compose.animation.core.animateDpAsState
import androidx.compose.animation.core.tween
import androidx.compose.animation.fadeIn
import androidx.compose.animation.fadeOut
import androidx.compose.animation.with
import androidx.compose.foundation.layout.Arrangement
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.PaddingValues
import androidx.compose.foundation.layout.Row
import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.layout.padding
import androidx.compose.foundation.rememberScrollState
import androidx.compose.foundation.shape.RoundedCornerShape
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.filled.Edit
import androidx.compose.material.icons.filled.ExpandLess
import androidx.compose.material.icons.filled.ExpandMore
import androidx.compose.material.icons.filled.Palette
import androidx.compose.material.icons.filled.Pause
import androidx.compose.material.icons.filled.PlayArrow
import androidx.compose.material.icons.filled.Settings
import androidx.compose.material.icons.filled.SkipNext
import androidx.compose.material.icons.filled.Speed
import androidx.compose.material.icons.outlined.Edit
import androidx.compose.material.icons.outlined.Palette
import androidx.compose.material.icons.outlined.Settings
import androidx.compose.material.icons.outlined.Speed
import androidx.compose.material3.Card
import androidx.compose.material3.CardDefaults
import androidx.compose.material3.ExperimentalMaterial3Api
import androidx.compose.material3.Icon
import androidx.compose.material3.IconButton
import androidx.compose.material3.IconToggleButton
import androidx.compose.material3.MaterialTheme
import androidx.compose.material3.NavigationBar
import androidx.compose.material3.NavigationBarItem
import androidx.compose.material3.Text
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.Shape
import androidx.compose.ui.layout.Layout
import androidx.compose.ui.layout.Measurable
import androidx.compose.ui.layout.layoutId
import androidx.compose.ui.res.stringResource
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.model.TemporalGameOfLifeState
import com.alexvanyo.composelife.navigation.NavigationHost
import com.alexvanyo.composelife.navigation.currentEntry
import com.alexvanyo.composelife.ui.R
import com.alexvanyo.composelife.ui.util.canScrollDown
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.launch

@Suppress("LongParameterList")
@Composable
fun CellUniverseActionCard(
    temporalGameOfLifeState: TemporalGameOfLifeState,
    isTopCard: Boolean,
    modifier: Modifier = Modifier,
    contentPadding: PaddingValues = PaddingValues(0.dp),
    shape: Shape = RoundedCornerShape(12.0.dp),
    actionCardState: CellUniverseActionCardState = rememberCellUniverseActionCardState(),
    coroutineScope: CoroutineScope = rememberCoroutineScope(),
) {
    CellUniverseActionCard(
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
        contentPadding = contentPadding,
        shape = shape,
        actionCardState = actionCardState,
        modifier = modifier,
    )
}

@Suppress("LongParameterList", "LongMethod")
@OptIn(ExperimentalMaterial3Api::class, ExperimentalAnimationApi::class)
@Composable
fun CellUniverseActionCard(
    isTopCard: Boolean,
    isRunning: Boolean,
    setIsRunning: (Boolean) -> Unit,
    onStep: () -> Unit,
    targetStepsPerSecond: Double,
    setTargetStepsPerSecond: (Double) -> Unit,
    generationsPerStep: Int,
    setGenerationsPerStep: (Int) -> Unit,
    modifier: Modifier = Modifier,
    contentPadding: PaddingValues = PaddingValues(0.dp),
    shape: Shape = RoundedCornerShape(12.0.dp),
    actionCardState: CellUniverseActionCardState = rememberCellUniverseActionCardState(),
) {
    Card(
        shape = shape,
        containerColor = MaterialTheme.colorScheme.surface,
        elevation = CardDefaults.cardElevation(
            defaultElevation = 1.dp
        ),
        modifier = modifier,
    ) {
        Column(
            horizontalAlignment = Alignment.CenterHorizontally,
            modifier = Modifier.padding(contentPadding)
        ) {
            AnimatedVisibility(visible = !actionCardState.isFullscreen) {
                ActionControlRow(
                    isRunning = isRunning,
                    setIsRunning = setIsRunning,
                    onStep = onStep,
                    isExpanded = actionCardState.isExpanded,
                    setIsExpanded = { actionCardState.isExpanded = it },
                )
            }

            if (actionCardState.isExpanded && actionCardState.canNavigateBack) {
                BackHandler(enabled = isTopCard) {
                    actionCardState.onBackPressed(actionCardState.navigationState.currentEntryId)
                }
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
                    val contentScrollStateMap =
                        actionCardState.navigationState.entryMap.mapValues { (entryId, _) ->
                            key(entryId) {
                                rememberScrollState()
                            }
                        }

                    Layout(
                        content = {
                            val currentScrollState = contentScrollStateMap.getValue(
                                actionCardState.navigationState.currentEntryId
                            )

                            ActionCardNavigationBar(
                                actionCardState = actionCardState,
                                isElevated = currentScrollState.canScrollDown,
                                modifier = Modifier.layoutId(ActionCardDestinationLayoutTypes.BottomBar)
                            )

                            NavigationHost(
                                navigationState = actionCardState.navigationState,
                                transitionSpec = {
                                    fadeIn(animationSpec = tween(220, delayMillis = 90)) with
                                        fadeOut(animationSpec = tween(90))
                                },
                                contentAlignment = Alignment.BottomCenter,
                                modifier = Modifier
                                    .layoutId(ActionCardDestinationLayoutTypes.NavHost)
                                    .animateContentSize()
                            ) { entry ->
                                // Cache the scroll state based for the target entry id.
                                // This value won't change normally, but it will ensure we keep using the old state
                                // while being removed from the backstack
                                val scrollState = remember { contentScrollStateMap.getValue(entry.id) }

                                when (entry.value) {
                                    ActionCardNavigation.Speed -> SpeedScreen(
                                        targetStepsPerSecond = targetStepsPerSecond,
                                        setTargetStepsPerSecond = setTargetStepsPerSecond,
                                        generationsPerStep = generationsPerStep,
                                        setGenerationsPerStep = setGenerationsPerStep,
                                        scrollState = scrollState,
                                        modifier = Modifier.fillMaxWidth()
                                    )
                                    ActionCardNavigation.Edit -> Spacer(modifier = Modifier.fillMaxWidth())
                                    ActionCardNavigation.Palette -> PaletteScreen(
                                        scrollState = scrollState,
                                        modifier = Modifier.fillMaxWidth()
                                    )
                                    ActionCardNavigation.Settings -> {
                                        Column(
                                            modifier = Modifier.fillMaxWidth()
                                        ) {
                                            Spacer(Modifier.weight(1f))
                                        }
                                    }
                                }
                            }
                        },
                        measurePolicy = { measurables, constraints ->
                            lateinit var bottomBarMeasurable: Measurable
                            lateinit var navHostMeasurable: Measurable

                            measurables.forEach {
                                when (it.layoutId as ActionCardDestinationLayoutTypes) {
                                    ActionCardDestinationLayoutTypes.BottomBar -> bottomBarMeasurable = it
                                    ActionCardDestinationLayoutTypes.NavHost -> navHostMeasurable = it
                                }
                            }

                            val bottomBarIntrinsicHeight = bottomBarMeasurable.minIntrinsicHeight(constraints.maxWidth)

                            val bottomBarPlaceable = bottomBarMeasurable.measure(
                                constraints.copy(
                                    maxHeight = bottomBarIntrinsicHeight
                                )
                            )

                            val navHostPlaceable = navHostMeasurable.measure(
                                constraints.copy(
                                    maxHeight = constraints.maxHeight - bottomBarPlaceable.height
                                )
                            )

                            layout(constraints.maxWidth, bottomBarPlaceable.height + navHostPlaceable.height) {
                                navHostPlaceable.place(0, 0)
                                bottomBarPlaceable.place(0, navHostPlaceable.height)
                            }
                        },
                        modifier = Modifier.padding(top = 8.dp)
                    )
                }
            }
        }
    }
}

private sealed interface ActionCardDestinationLayoutTypes {
    object BottomBar : ActionCardDestinationLayoutTypes
    object NavHost : ActionCardDestinationLayoutTypes
}

@Suppress("LongMethod")
@Composable
fun ActionCardNavigationBar(
    actionCardState: CellUniverseActionCardState,
    isElevated: Boolean,
    modifier: Modifier = Modifier,
) {
    val elevation by animateDpAsState(targetValue = if (isElevated) 3.dp else 0.dp)

    NavigationBar(
        modifier = modifier,
        tonalElevation = elevation
    ) {
        val speedSelected =
            actionCardState.navigationState.currentEntry.value == ActionCardNavigation.Speed
        val editSelected =
            actionCardState.navigationState.currentEntry.value == ActionCardNavigation.Edit
        val paletteSelected =
            actionCardState.navigationState.currentEntry.value == ActionCardNavigation.Palette
        val settingsSelected =
            actionCardState.navigationState.currentEntry.value == ActionCardNavigation.Settings

        NavigationBarItem(
            selected = speedSelected,
            onClick = actionCardState::onSpeedClicked,
            icon = {
                Icon(
                    if (speedSelected) {
                        Icons.Filled.Speed
                    } else {
                        Icons.Outlined.Speed
                    },
                    contentDescription = ""
                )
            },
            label = {
                Text(text = stringResource(id = R.string.speed))
            },
        )
        NavigationBarItem(
            selected = editSelected,
            onClick = actionCardState::onEditClicked,
            icon = {
                Icon(
                    if (editSelected) {
                        Icons.Filled.Edit
                    } else {
                        Icons.Outlined.Edit
                    },
                    contentDescription = ""
                )
            },
            label = {
                Text(text = stringResource(id = R.string.edit))
            },
        )
        NavigationBarItem(
            selected = paletteSelected,
            onClick = actionCardState::onPaletteClicked,
            icon = {
                Icon(
                    if (paletteSelected) {
                        Icons.Filled.Palette
                    } else {
                        Icons.Outlined.Palette
                    },
                    contentDescription = ""
                )
            },
            label = {
                Text(text = stringResource(id = R.string.palette))
            },
        )
        NavigationBarItem(
            selected = settingsSelected,
            onClick = actionCardState::onSettingsClicked,
            icon = {
                Icon(
                    if (settingsSelected) {
                        Icons.Filled.Settings
                    } else {
                        Icons.Outlined.Settings
                    },
                    contentDescription = ""
                )
            },
            label = {
                Text(text = stringResource(id = R.string.settings))
            },
        )
    }
}

@Suppress("LongParameterList")
@Composable
private fun ActionControlRow(
    isRunning: Boolean,
    setIsRunning: (Boolean) -> Unit,
    onStep: () -> Unit,
    isExpanded: Boolean,
    setIsExpanded: (Boolean) -> Unit,
    modifier: Modifier = Modifier
) {
    Row(
        horizontalArrangement = Arrangement.spacedBy(8.dp),
        modifier = modifier
    ) {
        Spacer(modifier = Modifier.weight(1f, fill = false))

        IconToggleButton(
            checked = isRunning,
            onCheckedChange = setIsRunning,
        ) {
            Icon(
                imageVector = if (isRunning) {
                    Icons.Filled.Pause
                } else {
                    Icons.Filled.PlayArrow
                },
                contentDescription = if (isRunning) {
                    stringResource(id = R.string.pause)
                } else {
                    stringResource(id = R.string.play)
                }
            )
        }

        IconButton(
            onClick = onStep
        ) {
            Icon(
                imageVector = Icons.Filled.SkipNext,
                contentDescription = stringResource(id = R.string.step)
            )
        }

        IconToggleButton(
            checked = isExpanded,
            onCheckedChange = setIsExpanded,
        ) {
            Icon(
                imageVector = if (isExpanded) {
                    Icons.Filled.ExpandMore
                } else {
                    Icons.Filled.ExpandLess
                },
                contentDescription = if (isExpanded) {
                    stringResource(id = R.string.collapse)
                } else {
                    stringResource(id = R.string.expand)
                }
            )
        }

        Spacer(modifier = Modifier.weight(1f, fill = false))
    }
}
