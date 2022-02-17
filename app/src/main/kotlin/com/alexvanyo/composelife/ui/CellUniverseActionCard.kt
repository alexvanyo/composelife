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
import androidx.compose.material.icons.filled.Pause
import androidx.compose.material.icons.filled.PlayArrow
import androidx.compose.material.icons.filled.SkipNext
import androidx.compose.material3.Card
import androidx.compose.material3.ExperimentalMaterial3Api
import androidx.compose.material3.Icon
import androidx.compose.material3.IconButton
import androidx.compose.material3.IconToggleButton
import androidx.compose.material3.MaterialTheme
import androidx.compose.material3.Slider
import androidx.compose.material3.Text
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
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
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.launch
import kotlin.math.log2
import kotlin.math.pow
import kotlin.math.roundToInt

@Composable
fun CellUniverseActionCard(
    temporalGameOfLifeState: TemporalGameOfLifeState,
    modifier: Modifier = Modifier,
    coroutineScope: CoroutineScope = rememberCoroutineScope(),
) {
    CellUniverseActionCard(
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
        modifier = modifier,
    )
}

@Suppress("LongParameterList")
@OptIn(ExperimentalMaterial3Api::class, ExperimentalAnimationApi::class)
@Composable
fun CellUniverseActionCard(
    isRunning: Boolean,
    setIsRunning: (Boolean) -> Unit,
    onStep: () -> Unit,
    targetStepsPerSecond: Double,
    setTargetStepsPerSecond: (Double) -> Unit,
    generationsPerStep: Int,
    setGenerationsPerStep: (Int) -> Unit,
    modifier: Modifier = Modifier,
) {
    Card(modifier = modifier) {
        var isExpanded by rememberSaveable { mutableStateOf(false) }

        Column(
            horizontalAlignment = Alignment.CenterHorizontally,
            modifier = Modifier.padding(horizontal = 8.dp)
        ) {
            ActionControlRow(
                isRunning = isRunning,
                setIsRunning = setIsRunning,
                onStep = onStep,
                isExpanded = isExpanded,
                setIsExpanded = { isExpanded = it }
            )

            AnimatedContent(
                targetState = isExpanded,
                transitionSpec = {
                    fadeIn(animationSpec = tween(220, delayMillis = 90)) with
                        fadeOut(animationSpec = tween(90))
                },
                contentAlignment = Alignment.BottomCenter,
            ) { targetIsExpanded ->
                if (targetIsExpanded) {
                    Column(
                        modifier = Modifier
                            .padding(top = 8.dp)
                            .padding(horizontal = 8.dp)
                    ) {
                        TargetStepsPerSecondControl(
                            targetStepsPerSecond = targetStepsPerSecond,
                            setTargetStepsPerSecond = setTargetStepsPerSecond
                        )

                        GenerationsPerStepControl(
                            generationsPerStep = generationsPerStep,
                            setGenerationsPerStep = setGenerationsPerStep
                        )
                    }
                }
            }
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
