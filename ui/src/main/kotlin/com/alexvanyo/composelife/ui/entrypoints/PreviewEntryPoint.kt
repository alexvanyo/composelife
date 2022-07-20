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
import com.alexvanyo.composelife.algorithm.di.GameOfLifeAlgorithmProvider
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.dispatchers.DefaultComposeLifeDispatchers
import com.alexvanyo.composelife.dispatchers.di.ComposeLifeDispatchersProvider
import com.alexvanyo.composelife.preferences.AlgorithmType
import com.alexvanyo.composelife.preferences.ComposeLifePreferences
import com.alexvanyo.composelife.preferences.CurrentShape
import com.alexvanyo.composelife.preferences.CurrentShapeType
import com.alexvanyo.composelife.preferences.DarkThemeConfig
import com.alexvanyo.composelife.preferences.TestComposeLifePreferences
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.random.di.RandomProvider
import com.alexvanyo.composelife.ui.InteractiveCellUniverseEntryPoint
import com.alexvanyo.composelife.ui.InteractiveCellUniverseOverlayEntryPoint
import com.alexvanyo.composelife.ui.action.CellUniverseActionCardEntryPoint
import com.alexvanyo.composelife.ui.action.InlinePaletteScreenEntryPoint
import com.alexvanyo.composelife.ui.action.settings.AlgorithmImplementationUiEntryPoint
import com.alexvanyo.composelife.ui.action.settings.DarkThemeConfigUiEntryPoint
import com.alexvanyo.composelife.ui.action.settings.FullscreenSettingsScreenEntryPoint
import com.alexvanyo.composelife.ui.action.settings.SettingUiEntryPoint
import com.alexvanyo.composelife.ui.component.GameOfLifeProgressIndicatorEntryPoint
import kotlin.random.Random

interface PreviewEntryPoint :
    AlgorithmImplementationUiEntryPoint,
    CellUniverseActionCardEntryPoint,
    DarkThemeConfigUiEntryPoint,
    FullscreenSettingsScreenEntryPoint,
    GameOfLifeProgressIndicatorEntryPoint,
    InlinePaletteScreenEntryPoint,
    InteractiveCellUniverseEntryPoint,
    InteractiveCellUniverseOverlayEntryPoint,
    SettingUiEntryPoint

/**
 * Provides fake implementations for the entry points passed to [content] as context receivers.
 *
 * This is useful for providing dependencies to previews where the full dependency graph isn't available.
 */
@Composable
fun WithPreviewDependencies(
    dispatchers: ComposeLifeDispatchers = DefaultComposeLifeDispatchers(),
    gameOfLifeAlgorithm: GameOfLifeAlgorithm = NaiveGameOfLifeAlgorithm(dispatchers),
    composeLifePreferences: ComposeLifePreferences = TestComposeLifePreferences.Loaded(
        algorithmChoice = AlgorithmType.NaiveAlgorithm,
        currentShapeType = CurrentShapeType.RoundRectangle,
        roundRectangleConfig = CurrentShape.RoundRectangle(
            sizeFraction = 1.0f,
            cornerFraction = 0.0f,
        ),
        darkThemeConfig = DarkThemeConfig.FollowSystem,
    ),
    random: Random = Random(0),
    content: @Composable context(PreviewEntryPoint) () -> Unit,
) {
    val dispatchersProvider = object : ComposeLifeDispatchersProvider {
        override val dispatchers = dispatchers
    }
    val algorithmProvider = object : GameOfLifeAlgorithmProvider {
        override val gameOfLifeAlgorithm = gameOfLifeAlgorithm
    }
    val preferencesProvider = object : ComposeLifePreferencesProvider {
        override val composeLifePreferences = composeLifePreferences
    }
    val randomProvider = object : RandomProvider {
        override val random = random
    }

    val entryPoint = object :
        PreviewEntryPoint,
        ComposeLifeDispatchersProvider by dispatchersProvider,
        GameOfLifeAlgorithmProvider by algorithmProvider,
        ComposeLifePreferencesProvider by preferencesProvider,
        RandomProvider by randomProvider {}

    content(entryPoint)
}
