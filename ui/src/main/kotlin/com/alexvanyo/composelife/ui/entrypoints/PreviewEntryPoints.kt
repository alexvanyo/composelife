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

package com.alexvanyo.composelife.ui.entrypoints

import androidx.compose.runtime.Composable
import com.alexvanyo.composelife.algorithm.GameOfLifeAlgorithm
import com.alexvanyo.composelife.algorithm.NaiveGameOfLifeAlgorithm
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.dispatchers.DefaultComposeLifeDispatchers
import com.alexvanyo.composelife.preferences.AlgorithmType
import com.alexvanyo.composelife.preferences.ComposeLifePreferences
import com.alexvanyo.composelife.preferences.CurrentShape
import com.alexvanyo.composelife.preferences.CurrentShapeType
import com.alexvanyo.composelife.preferences.DarkThemeConfig
import com.alexvanyo.composelife.preferences.TestComposeLifePreferences
import com.alexvanyo.composelife.ui.entrypoints.algorithm.GameOfLifeAlgorithmEntryPoint
import com.alexvanyo.composelife.ui.entrypoints.dispatchers.ComposeLifeDispatchersEntryPoint
import com.alexvanyo.composelife.ui.entrypoints.preferences.ComposeLifePreferencesEntryPoint

/**
 * Binds the given dependencies into context via their corresponding entry points.
 */
@Composable
fun WithDependencies(
    dispatchers: ComposeLifeDispatchers,
    gameOfLifeAlgorithm: GameOfLifeAlgorithm,
    composeLifePreferences: ComposeLifePreferences,
    content: @Composable context(
        ComposeLifeDispatchersEntryPoint,
        GameOfLifeAlgorithmEntryPoint,
        ComposeLifePreferencesEntryPoint
    ) () -> Unit,
) {
    val dispatchersEntryPoint = object : ComposeLifeDispatchersEntryPoint {
        override val dispatchers = dispatchers
    }
    val algorithmEntryPoint = object : GameOfLifeAlgorithmEntryPoint {
        override val gameOfLifeAlgorithm = gameOfLifeAlgorithm
    }
    val preferencesEntryPoint = object : ComposeLifePreferencesEntryPoint {
        override val composeLifePreferences = composeLifePreferences
    }

    content(
        dispatchersEntryPoint,
        algorithmEntryPoint,
        preferencesEntryPoint,
    )
}

/**
 * Provides fake implementations for the entry points passed to [content] as context receivers.
 *
 * This is useful for providing dependencies to previews where the full dependency graph isn't available.
 */
@Composable
fun WithPreviewDependencies(
    content: @Composable context(
        ComposeLifeDispatchersEntryPoint,
        GameOfLifeAlgorithmEntryPoint,
        ComposeLifePreferencesEntryPoint
    ) () -> Unit,
) {
    val dispatchers = DefaultComposeLifeDispatchers()
    WithDependencies(
        dispatchers = dispatchers,
        gameOfLifeAlgorithm = NaiveGameOfLifeAlgorithm(dispatchers),
        composeLifePreferences = TestComposeLifePreferences.Loaded(
            algorithmChoice = AlgorithmType.NaiveAlgorithm,
            currentShapeType = CurrentShapeType.RoundRectangle,
            roundRectangleConfig = CurrentShape.RoundRectangle(
                sizeFraction = 1.0f,
                cornerFraction = 0.0f,
            ),
            darkThemeConfig = DarkThemeConfig.FollowSystem,
        ),
        content = content,
    )
}
