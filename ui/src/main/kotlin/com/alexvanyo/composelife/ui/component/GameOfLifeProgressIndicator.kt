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

package com.alexvanyo.composelife.ui.component

import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.padding
import androidx.compose.foundation.layout.size
import androidx.compose.foundation.progressSemantics
import androidx.compose.material3.CircularProgressIndicator
import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.key
import androidx.compose.runtime.remember
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.platform.InfiniteAnimationPolicy
import androidx.compose.ui.platform.LocalLifecycleOwner
import androidx.compose.ui.unit.dp
import androidx.lifecycle.Lifecycle
import androidx.lifecycle.repeatOnLifecycle
import com.alexvanyo.composelife.algorithm.di.GameOfLifeAlgorithmProvider
import com.alexvanyo.composelife.dispatchers.di.ComposeLifeDispatchersProvider
import com.alexvanyo.composelife.model.GameOfLifeState
import com.alexvanyo.composelife.model.rememberTemporalGameOfLifeState
import com.alexvanyo.composelife.model.rememberTemporalGameOfLifeStateMutator
import com.alexvanyo.composelife.patterns.OscillatorPattern
import com.alexvanyo.composelife.patterns.values
import com.alexvanyo.composelife.preferences.CurrentShape
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.random.di.RandomProvider
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.ui.cells.NonInteractableCells
import com.alexvanyo.composelife.ui.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.theme.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.ThemePreviews
import dagger.hilt.EntryPoint
import dagger.hilt.InstallIn
import dagger.hilt.android.components.ActivityComponent
import kotlinx.coroutines.awaitCancellation
import kotlin.math.max
import kotlin.random.Random

@EntryPoint
@InstallIn(ActivityComponent::class)
interface GameOfLifeProgressIndicatorEntryPoint :
    GameOfLifeAlgorithmProvider,
    ComposeLifePreferencesProvider,
    ComposeLifeDispatchersProvider,
    RandomProvider

/**
 * A progress indicator that displays progress via an embedded set of cells displaying an
 * oscillating pattern.
 */
context(GameOfLifeProgressIndicatorEntryPoint)
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
            cellState = pattern.seedCellState,
            isRunning = false,
            targetStepsPerSecond = 4.0,
        )
    }

    key(pattern) {
        rememberTemporalGameOfLifeStateMutator(
            temporalGameOfLifeState = temporalGameOfLifeState,
            dispatchers = dispatchers,
            gameOfLifeAlgorithm = gameOfLifeAlgorithm,
        )
    }

    val lifecycleOwner = LocalLifecycleOwner.current
    LaunchedEffect(lifecycleOwner, temporalGameOfLifeState) {
        // If we are not visible, don't animate
        lifecycleOwner.repeatOnLifecycle(Lifecycle.State.STARTED) {
            try {
                // If we are in tests, avoid running the infinite animation
                // It's fine if we only check this upon being started
                if (coroutineContext[InfiniteAnimationPolicy] == null) {
                    temporalGameOfLifeState.setIsRunning(true)
                    awaitCancellation()
                }
            } finally {
                temporalGameOfLifeState.setIsRunning(false)
            }
        }
    }

    GameOfLifeProgressIndicator(
        pattern = pattern,
        gameOfLifeState = temporalGameOfLifeState,
        currentShapeState = composeLifePreferences.currentShapeState,
        modifier = modifier,
    )
}

@Composable
fun GameOfLifeProgressIndicator(
    pattern: OscillatorPattern,
    gameOfLifeState: GameOfLifeState,
    currentShapeState: ResourceState<CurrentShape>,
    modifier: Modifier = Modifier,
) {
    Box(
        modifier = modifier
            .size(64.dp)
            .padding(8.dp),
        contentAlignment = Alignment.Center,
    ) {
        when (currentShapeState) {
            ResourceState.Loading, is ResourceState.Failure -> {
                // If we don't know the shape, fallback to a standard progress indicator
                CircularProgressIndicator()
            }
            is ResourceState.Success -> {
                NonInteractableCells(
                    gameOfLifeState = gameOfLifeState,
                    scaledCellDpSize = 48.dp / max(
                        pattern.boundingBox.width + 1,
                        pattern.boundingBox.height + 1,
                    ),
                    cellWindow = pattern.boundingBox.inflate(1),
                    shape = currentShapeState.value,
                    modifier = Modifier
                        .progressSemantics(),
                )
            }
        }
    }
}

@ThemePreviews
@Composable
fun GameOfLifeProgressIndicatorBlinkerPreview() {
    WithPreviewDependencies(
        random = Random(2),
    ) {
        ComposeLifeTheme {
            GameOfLifeProgressIndicator()
        }
    }
}

@ThemePreviews
@Composable
fun GameOfLifeProgressIndicatorToadPreview() {
    WithPreviewDependencies(
        random = Random(5),
    ) {
        ComposeLifeTheme {
            GameOfLifeProgressIndicator()
        }
    }
}

@ThemePreviews
@Composable
fun GameOfLifeProgressIndicatorBeaconPreview() {
    WithPreviewDependencies(
        random = Random(0),
    ) {
        ComposeLifeTheme {
            GameOfLifeProgressIndicator()
        }
    }
}
