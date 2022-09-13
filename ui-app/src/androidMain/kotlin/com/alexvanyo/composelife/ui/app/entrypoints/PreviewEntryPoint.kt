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

package com.alexvanyo.composelife.ui.app.entrypoints

import androidx.compose.runtime.Composable
import androidx.compose.ui.platform.LocalContext
import androidx.room.Room
import com.alexvanyo.composelife.algorithm.GameOfLifeAlgorithm
import com.alexvanyo.composelife.algorithm.NaiveGameOfLifeAlgorithm
import com.alexvanyo.composelife.algorithm.di.GameOfLifeAlgorithmProvider
import com.alexvanyo.composelife.clock.di.ClockProvider
import com.alexvanyo.composelife.data.CellStateRepositoryImpl
import com.alexvanyo.composelife.data.di.CellStateRepositoryProvider
import com.alexvanyo.composelife.database.AppDatabase
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.dispatchers.DefaultComposeLifeDispatchers
import com.alexvanyo.composelife.dispatchers.di.ComposeLifeDispatchersProvider
import com.alexvanyo.composelife.model.FlexibleCellStateSerializer
import com.alexvanyo.composelife.preferences.ComposeLifePreferences
import com.alexvanyo.composelife.preferences.CurrentShape
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferences
import com.alexvanyo.composelife.preferences.TestComposeLifePreferences
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.di.LoadedComposeLifePreferencesProvider
import com.alexvanyo.composelife.random.di.RandomProvider
import com.alexvanyo.composelife.ui.app.ComposeLifeAppHiltEntryPoint
import com.alexvanyo.composelife.ui.app.InteractiveCellUniverseHiltEntryPoint
import com.alexvanyo.composelife.ui.app.InteractiveCellUniverseLocalEntryPoint
import com.alexvanyo.composelife.ui.app.InteractiveCellUniverseOverlayHiltEntryPoint
import com.alexvanyo.composelife.ui.app.InteractiveCellUniverseOverlayLocalEntryPoint
import com.alexvanyo.composelife.ui.app.action.CellUniverseActionCardHiltEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.AlgorithmImplementationUiHiltEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.AlgorithmImplementationUiLocalEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.CellShapeConfigUiHiltEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.CellShapeConfigUiLocalEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.CellStatePreviewUiLocalEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.DarkThemeConfigUiHiltEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.DarkThemeConfigUiLocalEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.DisableAGSLUiHiltEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.DisableAGSLUiLocalEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.DisableOpenGLUiHiltEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.DisableOpenGLUiLocalEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.FullscreenSettingsScreenHiltEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.FullscreenSettingsScreenLocalEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.InlineSettingsScreenHiltEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.InlineSettingsScreenLocalEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.SettingUiHiltEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.SettingUiLocalEntryPoint
import com.alexvanyo.composelife.ui.app.cells.CellWindowLocalEntryPoint
import com.alexvanyo.composelife.ui.app.cells.InteractableCellsLocalEntryPoint
import com.alexvanyo.composelife.ui.app.cells.NonInteractableCellsLocalEntryPoint
import com.alexvanyo.composelife.ui.app.component.GameOfLifeProgressIndicatorHiltEntryPoint
import com.alexvanyo.composelife.ui.app.component.GameOfLifeProgressIndicatorLocalEntryPoint
import kotlinx.datetime.Clock
import kotlin.random.Random

/**
 * The full super-interface implementing all entry points for rendering
 * previews in this module.
 */
internal interface PreviewEntryPoint :
    AlgorithmImplementationUiHiltEntryPoint,
    AlgorithmImplementationUiLocalEntryPoint,
    CellShapeConfigUiHiltEntryPoint,
    CellShapeConfigUiLocalEntryPoint,
    CellStatePreviewUiLocalEntryPoint,
    CellWindowLocalEntryPoint,
    CellUniverseActionCardHiltEntryPoint,
    ComposeLifeAppHiltEntryPoint,
    DarkThemeConfigUiHiltEntryPoint,
    DarkThemeConfigUiLocalEntryPoint,
    DisableAGSLUiHiltEntryPoint,
    DisableAGSLUiLocalEntryPoint,
    DisableOpenGLUiHiltEntryPoint,
    DisableOpenGLUiLocalEntryPoint,
    FullscreenSettingsScreenHiltEntryPoint,
    FullscreenSettingsScreenLocalEntryPoint,
    GameOfLifeProgressIndicatorHiltEntryPoint,
    GameOfLifeProgressIndicatorLocalEntryPoint,
    InlineSettingsScreenHiltEntryPoint,
    InlineSettingsScreenLocalEntryPoint,
    InteractableCellsLocalEntryPoint,
    InteractiveCellUniverseHiltEntryPoint,
    InteractiveCellUniverseLocalEntryPoint,
    InteractiveCellUniverseOverlayHiltEntryPoint,
    InteractiveCellUniverseOverlayLocalEntryPoint,
    NonInteractableCellsLocalEntryPoint,
    SettingUiHiltEntryPoint,
    SettingUiLocalEntryPoint

/**
 * Provides fake implementations for the entry points passed to [content] as context receivers.
 *
 * This is useful for providing dependencies to previews where the full dependency graph isn't available.
 */
@Suppress("LongParameterList")
@Composable
internal fun WithPreviewDependencies(
    dispatchers: ComposeLifeDispatchers = DefaultComposeLifeDispatchers(),
    gameOfLifeAlgorithm: GameOfLifeAlgorithm = NaiveGameOfLifeAlgorithm(dispatchers),
    loadedComposeLifePreferences: LoadedComposeLifePreferences = LoadedComposeLifePreferences.Defaults,
    composeLifePreferences: ComposeLifePreferences = TestComposeLifePreferences.Loaded(
        algorithmChoice = loadedComposeLifePreferences.algorithmChoice,
        currentShapeType = loadedComposeLifePreferences.currentShape.type,
        roundRectangleConfig = when (loadedComposeLifePreferences.currentShape) {
            is CurrentShape.RoundRectangle -> loadedComposeLifePreferences.currentShape as CurrentShape.RoundRectangle
            is CurrentShape.Superellipse -> TestComposeLifePreferences.defaultRoundRectangleConfig
        },
        superellipseConfig = when (loadedComposeLifePreferences.currentShape) {
            is CurrentShape.RoundRectangle -> TestComposeLifePreferences.defaultSuperellipseConfig
            is CurrentShape.Superellipse -> loadedComposeLifePreferences.currentShape as CurrentShape.Superellipse
        },
        darkThemeConfig = loadedComposeLifePreferences.darkThemeConfig,
        disableAGSL = loadedComposeLifePreferences.disableAGSL,
        disableOpenGL = loadedComposeLifePreferences.disableOpenGL,
    ),
    random: Random = Random(0),
    clock: Clock = Clock.System,
    content: @Composable context(PreviewEntryPoint) () -> Unit,
) {
    val appDatabase = Room.inMemoryDatabaseBuilder(LocalContext.current, AppDatabase::class.java).build()
    val cellStateDao = appDatabase.cellStateDao()

    val dispatchersProvider = object : ComposeLifeDispatchersProvider {
        override val dispatchers = dispatchers
    }
    val algorithmProvider = object : GameOfLifeAlgorithmProvider {
        override val gameOfLifeAlgorithm = gameOfLifeAlgorithm
    }
    val preferencesProvider = object : ComposeLifePreferencesProvider {
        override val composeLifePreferences = composeLifePreferences
    }
    val cellStateRepositoryProvider = object : CellStateRepositoryProvider {
        override val cellStateRepository = CellStateRepositoryImpl(
            flexibleCellStateSerializer = FlexibleCellStateSerializer(dispatchers),
            cellStateDao = cellStateDao,
        )
    }
    val loadedPreferencesProvider = object : LoadedComposeLifePreferencesProvider {
        override val preferences: LoadedComposeLifePreferences = loadedComposeLifePreferences
    }
    val randomProvider = object : RandomProvider {
        override val random = random
    }
    val clockProvider = object : ClockProvider {
        override val clock = clock
    }

    val entryPoint = object :
        PreviewEntryPoint,
        ComposeLifeDispatchersProvider by dispatchersProvider,
        GameOfLifeAlgorithmProvider by algorithmProvider,
        ComposeLifePreferencesProvider by preferencesProvider,
        CellStateRepositoryProvider by cellStateRepositoryProvider,
        LoadedComposeLifePreferencesProvider by loadedPreferencesProvider,
        RandomProvider by randomProvider,
        ClockProvider by clockProvider {}

    content(entryPoint)
}
