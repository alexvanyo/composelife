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
import androidx.compose.foundation.rememberScrollState
import androidx.compose.foundation.verticalScroll
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.filled.ArrowDropDown
import androidx.compose.material.icons.filled.ArrowDropUp
import androidx.compose.material.icons.filled.Pause
import androidx.compose.material.icons.filled.PlayArrow
import androidx.compose.material.icons.filled.SkipNext
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
import androidx.compose.runtime.saveable.Saver
import androidx.compose.runtime.saveable.SaverScope
import androidx.compose.runtime.saveable.listSaver
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
import com.alexvanyo.composelife.ui.navigation.Backstack
import com.alexvanyo.composelife.ui.navigation.BackstackEntry
import com.alexvanyo.composelife.ui.navigation.backstackBackHandler
import com.alexvanyo.composelife.ui.navigation.navigate
import com.alexvanyo.composelife.ui.navigation.popUpTo
import com.alexvanyo.composelife.ui.navigation.rememberBackstack
import com.livefront.sealedenum.GenSealedEnum
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
    initialBackstack: List<BackstackEntry<ActionCardNavigation>> = listOf(BackstackEntry(ActionCardNavigation.Speed))
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
                popUpToSpeed()
                backstack.navigate(ActionCardNavigation.Edit)
            }

            override fun onPaletteClicked() {
                popUpToSpeed()
                backstack.navigate(ActionCardNavigation.Palette)
            }

            override fun onSettingsClicked() {
                popUpToSpeed()
                backstack.navigate(ActionCardNavigation.Settings)
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
                                ActionCardNavigation.Palette -> Unit
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

@Composable
fun SpeedScreen(
    targetStepsPerSecond: Double,
    setTargetStepsPerSecond: (Double) -> Unit,
    generationsPerStep: Int,
    setGenerationsPerStep: (Int) -> Unit,
    modifier: Modifier = Modifier,
) {
    Column(
        modifier = modifier.verticalScroll(rememberScrollState())
    ) {
        TargetStepsPerSecondControl(
            targetStepsPerSecond = targetStepsPerSecond,
            setTargetStepsPerSecond = setTargetStepsPerSecond,
            modifier = Modifier.padding(horizontal = 16.dp)
        )

        GenerationsPerStepControl(
            generationsPerStep = generationsPerStep,
            setGenerationsPerStep = setGenerationsPerStep,
            modifier = Modifier.padding(horizontal = 16.dp)
        )
    }
}

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

        NavigationBarItem(
            selected = actionCardState.backstack.last().value == ActionCardNavigation.Speed,
            onClick = actionCardState::onSpeedClicked,
            icon = {
                Icon(
                    Icons.Outlined.Speed, contentDescription = ""
                )
            },
            label = {
                Text(text = stringResource(id = R.string.speed))
            },
            colors = navigationItemColors,
        )
        NavigationBarItem(
            selected = actionCardState.backstack.last().value == ActionCardNavigation.Edit,
            onClick = actionCardState::onEditClicked,
            icon = {
                Icon(Icons.Outlined.Edit, contentDescription = "")
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
                Icon(Icons.Outlined.Palette, contentDescription = "")
            },
            label = {
                Text(text = stringResource(id = R.string.palette))
            },
            colors = navigationItemColors,
        )
        NavigationBarItem(
            selected = actionCardState.backstack.last().value == ActionCardNavigation.Settings,
            onClick = actionCardState::onSettingsClicked,
            icon = {
                Icon(Icons.Outlined.Settings, contentDescription = "")
            },
            label = {
                Text(text = stringResource(id = R.string.settings))
            },
            colors = navigationItemColors,
        )
    }
}

sealed interface ActionCardNavigation {
    val type: ActionCardNavigationType<ActionCardNavigation>

    object Speed : ActionCardNavigation {
        override val type = ActionCardNavigationType.Speed
    }

    object Edit : ActionCardNavigation {
        override val type = ActionCardNavigationType.Edit
    }

    object Palette : ActionCardNavigation {
        override val type = ActionCardNavigationType.Palette
    }

    object Settings : ActionCardNavigation {
        override val type = ActionCardNavigationType.Settings
    }

    companion object {
        val Saver: Saver<ActionCardNavigation, Any> = listSaver(
            save = { actionCardNavigation ->
                listOf(
                    with(ActionCardNavigationType.Saver) { save(actionCardNavigation.type) },
                    save(actionCardNavigation = actionCardNavigation)
                )
            },
            restore = { list ->
                val type = ActionCardNavigationType.Saver.restore(list[0] as Int)!!
                type.saver.restore(list[1]!!)
            }
        )
    }
}

fun SaverScope.save(actionCardNavigation: ActionCardNavigation): Any? =
    when (actionCardNavigation) {
        is ActionCardNavigation.Speed -> with(actionCardNavigation.type.saver) { save(actionCardNavigation) }
        is ActionCardNavigation.Edit -> with(actionCardNavigation.type.saver) { save(actionCardNavigation) }
        is ActionCardNavigation.Palette -> with(actionCardNavigation.type.saver) { save(actionCardNavigation) }
        is ActionCardNavigation.Settings -> with(actionCardNavigation.type.saver) { save(actionCardNavigation) }
    }

/**
 * The type for each [ActionCardNavigation].
 *
 * These classes must be objects, since they need to statically be able to save and restore concrete
 * [ActionCardNavigation] types.
 */
sealed interface ActionCardNavigationType<out T : ActionCardNavigation> {
    val saver: Saver<out T, Any>

    object Speed : ActionCardNavigationType<ActionCardNavigation.Speed> {
        override val saver: Saver<ActionCardNavigation.Speed, Any> = Saver(
            save = { 0 },
            restore = { ActionCardNavigation.Speed }
        )
    }

    object Edit : ActionCardNavigationType<ActionCardNavigation.Edit> {
        override val saver: Saver<ActionCardNavigation.Edit, Any> = Saver(
            save = { 0 },
            restore = { ActionCardNavigation.Edit }
        )
    }

    object Palette : ActionCardNavigationType<ActionCardNavigation.Palette> {
        override val saver: Saver<ActionCardNavigation.Palette, Any> = Saver(
            save = { 0 },
            restore = { ActionCardNavigation.Palette }
        )
    }

    object Settings : ActionCardNavigationType<ActionCardNavigation.Settings> {
        override val saver: Saver<ActionCardNavigation.Settings, Any> = Saver(
            save = { 0 },
            restore = { ActionCardNavigation.Settings }
        )
    }

    @GenSealedEnum
    companion object {
        val Saver: Saver<ActionCardNavigationType<*>, Int> = object : Saver<ActionCardNavigationType<*>, Int> {
            override fun restore(value: Int): ActionCardNavigationType<*> =
                ActionCardNavigationTypeSealedEnum.values[value]

            override fun SaverScope.save(value: ActionCardNavigationType<*>): Int =
                value.ordinal
        }
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
