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
import androidx.compose.ui.semantics.clearAndSetSemantics
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.algorithm.di.GameOfLifeAlgorithmProvider
import com.alexvanyo.composelife.clock.di.ClockProvider
import com.alexvanyo.composelife.dispatchers.di.ComposeLifeDispatchersProvider
import com.alexvanyo.composelife.model.GameOfLifeState
import com.alexvanyo.composelife.model.TemporalGameOfLifeState
import com.alexvanyo.composelife.model.rememberTemporalGameOfLifeState
import com.alexvanyo.composelife.model.rememberTemporalGameOfLifeStateMutator
import com.alexvanyo.composelife.patterns.OscillatorPattern
import com.alexvanyo.composelife.patterns.values
import com.alexvanyo.composelife.random.di.RandomProvider
import com.alexvanyo.composelife.ui.app.cells.CellWindowLocalEntryPoint
import com.alexvanyo.composelife.ui.app.cells.CellWindowState
import com.alexvanyo.composelife.ui.app.cells.ImmutableCellWindow
import com.alexvanyo.composelife.ui.app.cells.ViewportInteractionConfig
import kotlin.math.max

interface GameOfLifeProgressIndicatorInjectEntryPoint :
    GameOfLifeAlgorithmProvider,
    ComposeLifeDispatchersProvider,
    RandomProvider,
    ClockProvider

interface GameOfLifeProgressIndicatorLocalEntryPoint :
    CellWindowLocalEntryPoint

/**
 * A progress indicator that displays progress via an embedded set of cells displaying an
 * oscillating pattern.
 */
context(GameOfLifeProgressIndicatorInjectEntryPoint, GameOfLifeProgressIndicatorLocalEntryPoint)
@Composable
fun GameOfLifeProgressIndicator(
    modifier: Modifier = Modifier,
) {
    val patternIndex = remember(OscillatorPattern.values.size) {
        random.nextInt(OscillatorPattern.values.size)
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
        gameOfLifeAlgorithm = gameOfLifeAlgorithm,
        dispatchers = dispatchers,
        clock = clock,
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
expect fun GameOfLifeProgressIndicatorForegroundEffect(
    temporalGameOfLifeState: TemporalGameOfLifeState,
)

context(GameOfLifeProgressIndicatorLocalEntryPoint)
@Suppress("LongParameterList")
@Composable
fun GameOfLifeProgressIndicator(
    pattern: OscillatorPattern,
    gameOfLifeState: GameOfLifeState,
    modifier: Modifier = Modifier,
) {
    ImmutableCellWindow(
        gameOfLifeState = gameOfLifeState,
        modifier = modifier
            .size(64.dp)
            .clipToBounds()
            .progressSemantics()
            .clearAndSetSemantics {},
        viewportInteractionConfig = ViewportInteractionConfig.Fixed(
            cellWindowState = CellWindowState(
                offset = Offset(
                    pattern.boundingBox.width / 2f,
                    pattern.boundingBox.height / 2f,
                ),
                scale = 1f / max(
                    pattern.boundingBox.width + 1,
                    pattern.boundingBox.height + 1,
                ),
            ),
        ),
        cellDpSize = 48.dp,
    )
}
