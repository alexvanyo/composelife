@file:Suppress("MatchingDeclarationName")

package com.alexvanyo.composelife.ui

import androidx.activity.compose.BackHandler
import androidx.compose.animation.AnimatedContent
import androidx.compose.animation.ExperimentalAnimationApi
import androidx.compose.animation.core.tween
import androidx.compose.animation.fadeIn
import androidx.compose.animation.fadeOut
import androidx.compose.animation.with
import androidx.compose.foundation.layout.Arrangement
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.Row
import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.padding
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.filled.ArrowDropDown
import androidx.compose.material.icons.filled.ArrowDropUp
import androidx.compose.material.icons.filled.Edit
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
import androidx.compose.material3.ExperimentalMaterial3Api
import androidx.compose.material3.Icon
import androidx.compose.material3.IconButton
import androidx.compose.material3.IconToggleButton
import androidx.compose.material3.MaterialTheme
import androidx.compose.material3.NavigationBar
import androidx.compose.material3.NavigationBarItem
import androidx.compose.material3.NavigationBarItemDefaults
import androidx.compose.material3.Text
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.res.stringResource
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.model.TemporalGameOfLifeState
import com.alexvanyo.composelife.navigation.BackstackEntry
import com.alexvanyo.composelife.navigation.BackstackState
import com.alexvanyo.composelife.navigation.NavigationHost
import com.alexvanyo.composelife.navigation.canNavigateBack
import com.alexvanyo.composelife.navigation.currentEntry
import com.alexvanyo.composelife.navigation.navigate
import com.alexvanyo.composelife.navigation.popBackstack
import com.alexvanyo.composelife.navigation.popUpTo
import com.alexvanyo.composelife.navigation.rememberMutableBackstackNavigationController
import com.alexvanyo.composelife.navigation.withExpectedActor
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.launch
import java.util.UUID

/**
 * The persistable state describing the [CellUniverseActionCard].
 */
interface CellUniverseActionCardState {

    /**
     * `true` if the card is expanded.
     */
    var isExpanded: Boolean

    val isFullscreen: Boolean

    val navigationState: BackstackState<ActionCardNavigation>

    val canNavigateBack: Boolean

    fun onSpeedClicked(actorBackstackEntryId: UUID? = null)

    fun onEditClicked(actorBackstackEntryId: UUID? = null)

    fun onPaletteClicked(actorBackstackEntryId: UUID? = null)

    fun onSettingsClicked(actorBackstackEntryId: UUID? = null)

    fun onBackPressed(actorBackstackEntryId: UUID? = null)

    companion object {
        const val defaultIsExpanded: Boolean = false
    }
}

/**
 * Remembers the a default implementation of [CellUniverseActionCardState].
 */
@Composable
fun rememberCellUniverseActionCardState(
    initialIsExpanded: Boolean = CellUniverseActionCardState.defaultIsExpanded,
    initialBackstackEntries: List<BackstackEntry<ActionCardNavigation>> = listOf(
        BackstackEntry(
            value = ActionCardNavigation.Speed,
            previous = null
        )
    )
): CellUniverseActionCardState {
    val isExpanded = rememberSaveable { mutableStateOf(initialIsExpanded) }

    val navController = rememberMutableBackstackNavigationController(
        initialBackstackEntries = initialBackstackEntries,
        saver = ActionCardNavigation.Saver
    )

    return remember {
        object : CellUniverseActionCardState {
            override var isExpanded: Boolean by isExpanded

            override val navigationState get() = navController

            override val canNavigateBack: Boolean get() = navController.canNavigateBack

            override val isFullscreen: Boolean get() =
                this.isExpanded && when (navigationState.currentEntry.value) {
                    ActionCardNavigation.Speed,
                    ActionCardNavigation.Edit,
                    ActionCardNavigation.Palette -> false
                    ActionCardNavigation.Settings -> true
                }

            override fun onSpeedClicked(actorBackstackEntryId: UUID?) {
                navController.withExpectedActor(actorBackstackEntryId) {
                    popUpToSpeed()
                }
            }

            override fun onEditClicked(actorBackstackEntryId: UUID?) {
                navController.withExpectedActor(actorBackstackEntryId) {
                    if (currentEntry.value !is ActionCardNavigation.Edit) {
                        popUpToSpeed()
                        navController.navigate(ActionCardNavigation.Edit)
                    }
                }
            }

            override fun onPaletteClicked(actorBackstackEntryId: UUID?) {
                navController.withExpectedActor(actorBackstackEntryId) {
                    if (currentEntry.value !is ActionCardNavigation.Palette) {
                        popUpToSpeed()
                        navController.navigate(ActionCardNavigation.Palette)
                    }
                }
            }

            override fun onSettingsClicked(actorBackstackEntryId: UUID?) {
                navController.withExpectedActor(actorBackstackEntryId) {
                    if (currentEntry.value !is ActionCardNavigation.Settings) {
                        popUpToSpeed()
                        navController.navigate(ActionCardNavigation.Settings)
                    }
                }
            }

            override fun onBackPressed(actorBackstackEntryId: UUID?) {
                navController.withExpectedActor(actorBackstackEntryId) {
                    navController.popBackstack()
                }
            }

            private fun popUpToSpeed() {
                navController.popUpTo(
                    predicate = { value: ActionCardNavigation ->
                        when (value) {
                            ActionCardNavigation.Speed -> true
                            ActionCardNavigation.Edit,
                            ActionCardNavigation.Palette,
                            ActionCardNavigation.Settings -> false
                        }
                    }
                )
            }
        }
    }
}

@Composable
fun CellUniverseActionCard(
    temporalGameOfLifeState: TemporalGameOfLifeState,
    isTopCard: Boolean,
    modifier: Modifier = Modifier,
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
        actionCardState = actionCardState,
        modifier = modifier,
    )
}

@Suppress("LongParameterList")
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
    actionCardState: CellUniverseActionCardState = rememberCellUniverseActionCardState(),
) {
    Card(modifier = modifier) {
        Column(
            horizontalAlignment = Alignment.CenterHorizontally,
        ) {
            ActionControlRow(
                isRunning = isRunning,
                setIsRunning = setIsRunning,
                onStep = onStep,
                isExpanded = actionCardState.isExpanded,
                setIsExpanded = { actionCardState.isExpanded = it },
            )

            AnimatedContent(
                targetState = actionCardState.isExpanded,
                transitionSpec = {
                    fadeIn(animationSpec = tween(220, delayMillis = 90)) with
                        fadeOut(animationSpec = tween(90))
                },
                contentAlignment = Alignment.BottomCenter,
            ) { isExpanded ->
                if (isExpanded) {
                    if (actionCardState.canNavigateBack) {
                        BackHandler(enabled = isTopCard) {
                            actionCardState.onBackPressed(actionCardState.navigationState.currentEntryId)
                        }
                    }

                    Column(
                        modifier = Modifier.padding(top = 8.dp)
                    ) {
                        NavigationHost(
                            navigationState = actionCardState.navigationState,
                            transitionSpec = {
                                fadeIn(animationSpec = tween(220, delayMillis = 90)) with
                                    fadeOut(animationSpec = tween(90))
                            }
                        ) { entry ->
                            when (entry.value) {
                                ActionCardNavigation.Speed -> SpeedScreen(
                                    targetStepsPerSecond = targetStepsPerSecond,
                                    setTargetStepsPerSecond = setTargetStepsPerSecond,
                                    generationsPerStep = generationsPerStep,
                                    setGenerationsPerStep = setGenerationsPerStep
                                )
                                ActionCardNavigation.Edit -> Unit
                                ActionCardNavigation.Palette -> PaletteScreen()
                                ActionCardNavigation.Settings -> Unit
                            }
                        }

                        Spacer(modifier = Modifier.weight(1f, fill = actionCardState.isFullscreen))

                        ActionCardNavigationBar(
                            actionCardState = actionCardState
                        )
                    }
                }
            }
        }
    }
}

@Suppress("LongMethod")
@Composable
fun ActionCardNavigationBar(
    actionCardState: CellUniverseActionCardState,
    modifier: Modifier = Modifier,
) {
    NavigationBar(
        containerColor = MaterialTheme.colorScheme.surfaceVariant,
        modifier = modifier,
    ) {
        val navigationItemColors = NavigationBarItemDefaults.colors(
            indicatorColor = MaterialTheme.colorScheme.tertiaryContainer
        )

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
            colors = navigationItemColors,
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
            colors = navigationItemColors,
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
            colors = navigationItemColors,
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
            colors = navigationItemColors,
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
                    Icons.Filled.ArrowDropDown
                } else {
                    Icons.Filled.ArrowDropUp
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
