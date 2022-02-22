@file:Suppress("MatchingDeclarationName")

package com.alexvanyo.composelife.ui

import androidx.compose.animation.AnimatedContent
import androidx.compose.animation.ExperimentalAnimationApi
import androidx.compose.animation.core.tween
import androidx.compose.animation.fadeIn
import androidx.compose.animation.fadeOut
import androidx.compose.animation.with
import androidx.compose.foundation.Canvas
import androidx.compose.foundation.layout.Arrangement
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.Row
import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.layout.height
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
import androidx.compose.material3.Slider
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
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.res.stringResource
import androidx.compose.ui.semantics.semantics
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.R
import com.alexvanyo.composelife.model.TemporalGameOfLifeState
import com.alexvanyo.composelife.navigation.Backstack
import com.alexvanyo.composelife.navigation.BackstackEntry
import com.alexvanyo.composelife.navigation.backstackBackHandler
import com.alexvanyo.composelife.navigation.navigate
import com.alexvanyo.composelife.navigation.popUpTo
import com.alexvanyo.composelife.navigation.rememberBackstack
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.launch
import kotlin.math.log2
import kotlin.math.pow
import kotlin.math.roundToInt

/**
 * The persistable state describing the [CellUniverseActionCard].
 */
interface CellUniverseActionCardState {

    /**
     * `true` if the card is expanded.
     */
    var isExpanded: Boolean

    val backstack: Backstack<ActionCardNavigation>

    val backstackBackHandler: @Composable (enabled: Boolean) -> Unit

    fun onSpeedClicked()

    fun onEditClicked()

    fun onPaletteClicked()

    fun onSettingsClicked()

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
    initialBackstack: Backstack<ActionCardNavigation> = listOf(BackstackEntry(ActionCardNavigation.Speed))
): CellUniverseActionCardState {
    var isExpanded by rememberSaveable { mutableStateOf(initialIsExpanded) }

    val backstack = rememberBackstack(
        initialBackstack = initialBackstack,
        saver = ActionCardNavigation.Saver
    )

    return remember {
        object : CellUniverseActionCardState {
            override var isExpanded: Boolean
                get() = isExpanded
                set(value) {
                    isExpanded = value
                }

            override val backstack: List<BackstackEntry<ActionCardNavigation>> = backstack

            override val backstackBackHandler get() = backstack.backstackBackHandler

            override fun onSpeedClicked() {
                popUpToSpeed()
            }

            override fun onEditClicked() {
                if (backstack.last().value !is ActionCardNavigation.Edit) {
                    popUpToSpeed()
                    backstack.navigate(ActionCardNavigation.Edit)
                }
            }

            override fun onPaletteClicked() {
                if (backstack.last().value !is ActionCardNavigation.Palette) {
                    popUpToSpeed()
                    backstack.navigate(ActionCardNavigation.Palette)
                }
            }

            override fun onSettingsClicked() {
                if (backstack.last().value !is ActionCardNavigation.Settings) {
                    popUpToSpeed()
                    backstack.navigate(ActionCardNavigation.Settings)
                }
            }

            private fun popUpToSpeed() {
                backstack.popUpTo(
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
                    actionCardState.backstackBackHandler(isTopCard)

                    Column(
                        modifier = Modifier.padding(top = 8.dp)
                    ) {
                        Backstack(
                            backstack = actionCardState.backstack,
                            transitionSpec = {
                                fadeIn(animationSpec = tween(220, delayMillis = 90)) with
                                    fadeOut(animationSpec = tween(90))
                            }
                        ) { entry ->
                            when (entry) {
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

        val speedSelected = actionCardState.backstack.last().value == ActionCardNavigation.Speed
        val editSelected = actionCardState.backstack.last().value == ActionCardNavigation.Edit
        val paletteSelected = actionCardState.backstack.last().value == ActionCardNavigation.Palette
        val settingsSelected = actionCardState.backstack.last().value == ActionCardNavigation.Settings

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
            selected = actionCardState.backstack.last().value == ActionCardNavigation.Palette,
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

@Composable
fun TargetStepsPerSecondControl(
    targetStepsPerSecond: Double,
    setTargetStepsPerSecond: (Double) -> Unit,
    modifier: Modifier = Modifier,
    minTargetStepsPerSecondPowerOfTwo: Int = 0,
    maxTargetStepsPerSecondPowerOfTwo: Int = 8
) {
    Column(modifier = modifier.semantics(mergeDescendants = true) {}) {
        Text(
            stringResource(id = R.string.target_steps_per_second, targetStepsPerSecond),
            modifier = Modifier.fillMaxWidth()
        )

        Box(
            contentAlignment = Alignment.Center
        ) {
            Slider(
                value = log2(targetStepsPerSecond).toFloat(),
                valueRange = minTargetStepsPerSecondPowerOfTwo.toFloat()..maxTargetStepsPerSecondPowerOfTwo.toFloat(),
                onValueChange = {
                    setTargetStepsPerSecond(2.0.pow(it.toDouble()))
                }
            )

            val tickColor = MaterialTheme.colorScheme.onSurfaceVariant

            Canvas(
                modifier = Modifier
                    .padding(horizontal = 10.dp)
                    .fillMaxWidth()
                    .height(24.dp)
            ) {
                val offsets = (minTargetStepsPerSecondPowerOfTwo..maxTargetStepsPerSecondPowerOfTwo).map {
                    (2f.pow(it) - 2f.pow(minTargetStepsPerSecondPowerOfTwo)) /
                        (2f.pow(maxTargetStepsPerSecondPowerOfTwo) - 2f.pow(minTargetStepsPerSecondPowerOfTwo))
                }

                offsets.forEach { xOffset ->
                    drawLine(
                        tickColor,
                        Offset(size.width * xOffset, 0f),
                        Offset(size.width * xOffset, size.height)
                    )
                }
            }
        }
    }
}

@Composable
fun GenerationsPerStepControl(
    generationsPerStep: Int,
    setGenerationsPerStep: (Int) -> Unit,
    modifier: Modifier = Modifier,
    minTargetStepsPerSecondPowerOfTwo: Int = 0,
    maxTargetStepsPerSecondPowerOfTwo: Int = 8
) {
    Column(modifier.semantics(mergeDescendants = true) {}) {
        Text(
            stringResource(id = R.string.generations_per_step, generationsPerStep),
            modifier = Modifier.fillMaxWidth()
        )

        Slider(
            value = log2(generationsPerStep.toFloat()),
            valueRange = minTargetStepsPerSecondPowerOfTwo.toFloat()..maxTargetStepsPerSecondPowerOfTwo.toFloat(),
            steps = maxTargetStepsPerSecondPowerOfTwo - minTargetStepsPerSecondPowerOfTwo - 1,
            onValueChange = {
                setGenerationsPerStep(2.0.pow(it.toDouble()).roundToInt())
            },
            onValueChangeFinished = {
                setGenerationsPerStep(2.0.pow(log2(generationsPerStep.toDouble()).roundToInt()).roundToInt())
            }
        )
    }
}
