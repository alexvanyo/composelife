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
import app.cash.sqldelight.driver.android.AndroidSqliteDriver
import com.alexvanyo.composelife.algorithm.GameOfLifeAlgorithm
import com.alexvanyo.composelife.algorithm.NaiveGameOfLifeAlgorithm
import com.alexvanyo.composelife.algorithm.di.GameOfLifeAlgorithmProvider
import com.alexvanyo.composelife.clock.di.ClockProvider
import com.alexvanyo.composelife.data.CellStateRepositoryImpl
import com.alexvanyo.composelife.data.di.CellStateRepositoryProvider
import com.alexvanyo.composelife.database.CellState
import com.alexvanyo.composelife.database.CellStateIdAdapter
import com.alexvanyo.composelife.database.ComposeLifeDatabase
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.dispatchers.DefaultComposeLifeDispatchers
import com.alexvanyo.composelife.dispatchers.di.ComposeLifeDispatchersProvider
import com.alexvanyo.composelife.model.CellStateParser
import com.alexvanyo.composelife.model.FlexibleCellStateSerializer
import com.alexvanyo.composelife.model.di.CellStateParserProvider
import com.alexvanyo.composelife.preferences.ComposeLifePreferences
import com.alexvanyo.composelife.preferences.CurrentShape
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferences
import com.alexvanyo.composelife.preferences.TestComposeLifePreferences
import com.alexvanyo.composelife.preferences.currentShape
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.di.LoadedComposeLifePreferencesProvider
import com.alexvanyo.composelife.random.di.RandomProvider
import com.alexvanyo.composelife.ui.app.CellUniversePaneInjectEntryPoint
import com.alexvanyo.composelife.ui.app.CellUniversePaneLocalEntryPoint
import com.alexvanyo.composelife.ui.app.ComposeLifeAppInjectEntryPoint
import com.alexvanyo.composelife.ui.app.InteractiveCellUniverseInjectEntryPoint
import com.alexvanyo.composelife.ui.app.InteractiveCellUniverseLocalEntryPoint
import com.alexvanyo.composelife.ui.app.InteractiveCellUniverseOverlayInjectEntryPoint
import com.alexvanyo.composelife.ui.app.InteractiveCellUniverseOverlayLocalEntryPoint
import com.alexvanyo.composelife.ui.app.action.CellUniverseActionCardInjectEntryPoint
import com.alexvanyo.composelife.ui.app.action.InlineEditPaneInjectEntryPoint
import com.alexvanyo.composelife.ui.app.action.InlineEditPaneLocalEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.AlgorithmImplementationUiInjectEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.AlgorithmImplementationUiLocalEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.CellShapeConfigUiInjectEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.CellShapeConfigUiLocalEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.CellStatePreviewUiInjectEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.CellStatePreviewUiLocalEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.DarkThemeConfigUiInjectEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.DarkThemeConfigUiLocalEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.DisableAGSLUiInjectEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.DisableAGSLUiLocalEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.DisableOpenGLUiInjectEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.DisableOpenGLUiLocalEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.EnableClipboardWatchingUiInjectEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.EnableClipboardWatchingUiLocalEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.FullscreenSettingsDetailPaneInjectEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.FullscreenSettingsDetailPaneLocalEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.InlineSettingsPaneInjectEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.InlineSettingsPaneLocalEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.SettingUiInjectEntryPoint
import com.alexvanyo.composelife.ui.app.action.settings.SettingUiLocalEntryPoint
import com.alexvanyo.composelife.ui.app.cells.CellWindowInjectEntryPoint
import com.alexvanyo.composelife.ui.app.cells.CellWindowLocalEntryPoint
import com.alexvanyo.composelife.ui.app.cells.InteractableCellsLocalEntryPoint
import com.alexvanyo.composelife.ui.app.cells.NonInteractableCellsLocalEntryPoint
import com.alexvanyo.composelife.ui.app.component.GameOfLifeProgressIndicatorInjectEntryPoint
import com.alexvanyo.composelife.ui.app.component.GameOfLifeProgressIndicatorLocalEntryPoint
import kotlinx.datetime.Clock
import kotlin.random.Random

/**
 * The full super-interface implementing all entry points for rendering
 * previews in this module.
 */
internal interface PreviewEntryPoint :
    AlgorithmImplementationUiInjectEntryPoint,
    AlgorithmImplementationUiLocalEntryPoint,
    CellShapeConfigUiInjectEntryPoint,
    CellShapeConfigUiLocalEntryPoint,
    CellStatePreviewUiInjectEntryPoint,
    CellStatePreviewUiLocalEntryPoint,
    CellWindowInjectEntryPoint,
    CellWindowLocalEntryPoint,
    CellUniverseActionCardInjectEntryPoint,
    CellUniversePaneInjectEntryPoint,
    CellUniversePaneLocalEntryPoint,
    ComposeLifeAppInjectEntryPoint,
    DarkThemeConfigUiInjectEntryPoint,
    DarkThemeConfigUiLocalEntryPoint,
    DisableAGSLUiInjectEntryPoint,
    DisableAGSLUiLocalEntryPoint,
    DisableOpenGLUiInjectEntryPoint,
    DisableOpenGLUiLocalEntryPoint,
    EnableClipboardWatchingUiInjectEntryPoint,
    EnableClipboardWatchingUiLocalEntryPoint,
    FullscreenSettingsDetailPaneInjectEntryPoint,
    FullscreenSettingsDetailPaneLocalEntryPoint,
    GameOfLifeProgressIndicatorInjectEntryPoint,
    GameOfLifeProgressIndicatorLocalEntryPoint,
    InlineEditPaneInjectEntryPoint,
    InlineEditPaneLocalEntryPoint,
    InlineSettingsPaneInjectEntryPoint,
    InlineSettingsPaneLocalEntryPoint,
    InteractableCellsLocalEntryPoint,
    InteractiveCellUniverseInjectEntryPoint,
    InteractiveCellUniverseLocalEntryPoint,
    InteractiveCellUniverseOverlayInjectEntryPoint,
    InteractiveCellUniverseOverlayLocalEntryPoint,
    NonInteractableCellsLocalEntryPoint,
    SettingUiInjectEntryPoint,
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
    composeLifePreferences: ComposeLifePreferences = TestComposeLifePreferences(
        algorithmChoice = loadedComposeLifePreferences.algorithmChoice,
        currentShapeType = loadedComposeLifePreferences.currentShape.type,
        roundRectangleConfig = when (loadedComposeLifePreferences.currentShape) {
            is CurrentShape.RoundRectangle -> loadedComposeLifePreferences.currentShape as CurrentShape.RoundRectangle
        },
        darkThemeConfig = loadedComposeLifePreferences.darkThemeConfig,
        disableAGSL = loadedComposeLifePreferences.disableAGSL,
        disableOpenGL = loadedComposeLifePreferences.disableOpenGL,
    ),
    random: Random = Random(1),
    clock: Clock = Clock.System,
    cellStateParser: CellStateParser = CellStateParser(
        flexibleCellStateSerializer = FlexibleCellStateSerializer(
            dispatchers = dispatchers,
        ),
        dispatchers = dispatchers,
        context = LocalContext.current,
    ),
    content: @Composable context(PreviewEntryPoint) () -> Unit,
) {
    val driver = AndroidSqliteDriver(
        schema = ComposeLifeDatabase.Schema,
        context = LocalContext.current,
        name = null,
    )
    val composeLifeDatabase = ComposeLifeDatabase(
        driver = driver,
        cellStateAdapter = CellState.Adapter(
            idAdapter = CellStateIdAdapter(),
        ),
    )
    val cellStateQueries = composeLifeDatabase.cellStateQueries

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
            cellStateQueries = cellStateQueries,
            dispatchers = dispatchers,
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
    val cellStateParserProvider = object : CellStateParserProvider {
        override val cellStateParser = cellStateParser
    }

    val entryPoint = object :
        PreviewEntryPoint,
        ComposeLifeDispatchersProvider by dispatchersProvider,
        GameOfLifeAlgorithmProvider by algorithmProvider,
        ComposeLifePreferencesProvider by preferencesProvider,
        CellStateRepositoryProvider by cellStateRepositoryProvider,
        LoadedComposeLifePreferencesProvider by loadedPreferencesProvider,
        RandomProvider by randomProvider,
        ClockProvider by clockProvider,
        CellStateParserProvider by cellStateParserProvider {}

    content(entryPoint)
}
