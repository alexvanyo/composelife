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

package com.alexvanyo.composelife.ui.app.component

import androidx.compose.foundation.layout.size
import androidx.compose.foundation.progressSemantics
import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.key
import androidx.compose.runtime.remember
import androidx.compose.ui.Modifier
import androidx.compose.ui.draw.clipToBounds
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.platform.InfiniteAnimationPolicy
import androidx.compose.ui.semantics.clearAndSetSemantics
import androidx.compose.ui.unit.dp
import androidx.lifecycle.Lifecycle
import androidx.lifecycle.compose.LocalLifecycleOwner
import androidx.lifecycle.repeatOnLifecycle
import com.alexvanyo.composelife.model.GameOfLifeState
import com.alexvanyo.composelife.model.TemporalGameOfLifeState
import com.alexvanyo.composelife.model.rememberTemporalGameOfLifeState
import com.alexvanyo.composelife.model.rememberTemporalGameOfLifeStateMutator
import com.alexvanyo.composelife.patterns.OscillatorPattern
import com.alexvanyo.composelife.patterns.values
import com.alexvanyo.composelife.sessionvalue.SessionValue
import com.alexvanyo.composelife.ui.cells.CellWindowInteractionState
import com.alexvanyo.composelife.ui.cells.CellWindowViewportState
import com.alexvanyo.composelife.ui.cells.ImmutableCellWindow
import com.alexvanyo.composelife.ui.cells.SelectionState
import com.alexvanyo.composelife.ui.cells.ViewportInteractionConfig
import kotlinx.coroutines.awaitCancellation
import kotlin.coroutines.coroutineContext
import kotlin.math.max
import kotlin.uuid.Uuid

/**
 * A progress indicator that displays progress via an embedded set of cells displaying an
 * oscillating pattern.
 */
context(injectEntryPoint: GameOfLifeProgressIndicatorInjectEntryPoint, _: GameOfLifeProgressIndicatorLocalEntryPoint)
@Composable
fun GameOfLifeProgressIndicator(
    modifier: Modifier = Modifier,
) {
    val patternIndex = remember(OscillatorPattern.values.size) {
        injectEntryPoint.random.nextInt(OscillatorPattern.values.size)
    }
    val pattern = OscillatorPattern.values[patternIndex]
    val temporalGameOfLifeState = key(pattern) {
        rememberTemporalGameOfLifeState(
            seedCellState = pattern.seedCellState,
            isRunning = false,
            targetStepsPerSecond = 4.0,
        )
    }

    val temporalGameOfLifeStateMutator = rememberTemporalGameOfLifeStateMutator(
        temporalGameOfLifeState = temporalGameOfLifeState,
        gameOfLifeAlgorithm = injectEntryPoint.gameOfLifeAlgorithm,
        dispatchers = injectEntryPoint.dispatchers,
        clock = injectEntryPoint.clock,
    )

    LaunchedEffect(temporalGameOfLifeStateMutator) {
        temporalGameOfLifeStateMutator.update()
    }

    GameOfLifeProgressIndicatorForegroundEffect(temporalGameOfLifeState)

    GameOfLifeProgressIndicator(
        pattern = pattern,
        gameOfLifeState = temporalGameOfLifeState,
        modifier = modifier,
    )
}

@Composable
fun GameOfLifeProgressIndicatorForegroundEffect(
    temporalGameOfLifeState: TemporalGameOfLifeState,
) {
    val lifecycleOwner = LocalLifecycleOwner.current
    LaunchedEffect(lifecycleOwner, temporalGameOfLifeState) {
        // If we are not visible, don't animate
        lifecycleOwner.repeatOnLifecycle(Lifecycle.State.STARTED) {
            try {
                withInfiniteAnimationPolicy {
                    temporalGameOfLifeState.setIsRunning(true)
                    awaitCancellation()
                }
            } finally {
                temporalGameOfLifeState.setIsRunning(false)
            }
        }
    }
}

private suspend fun <R> withInfiniteAnimationPolicy(block: suspend () -> R): R {
    val policy = coroutineContext[InfiniteAnimationPolicy]
    return if (policy == null) {
        block()
    } else {
        policy.onInfiniteOperation(block)
    }
}

context(_: GameOfLifeProgressIndicatorInjectEntryPoint, _: GameOfLifeProgressIndicatorLocalEntryPoint)
@Suppress("LongParameterList")
@Composable
fun GameOfLifeProgressIndicator(
    pattern: OscillatorPattern,
    gameOfLifeState: GameOfLifeState,
    modifier: Modifier = Modifier,
) {
    val selectionSessionState = remember {
        SessionValue(
            sessionId = Uuid.random(),
            valueId = Uuid.random(),
            value = SelectionState.NoSelection,
        )
    }
    ImmutableCellWindow(
        gameOfLifeState = gameOfLifeState,
        modifier = modifier
            .size(64.dp)
            .clipToBounds()
            .progressSemantics()
            .clearAndSetSemantics {},
        cellWindowInteractionState = CellWindowInteractionState(
            viewportInteractionConfig = ViewportInteractionConfig.Fixed(
                cellWindowViewportState = CellWindowViewportState(
                    offset = Offset(
                        (pattern.boundingBox.width - 1) / 2f,
                        (pattern.boundingBox.height - 1) / 2f,
                    ),
                    scale = 1f / max(
                        pattern.boundingBox.width,
                        pattern.boundingBox.height,
                    ),
                ),
            ),
            selectionSessionState = selectionSessionState,
        ),
        cellDpSize = 48.dp,
    )
}
