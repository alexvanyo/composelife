/*
 * Copyright 2024 The Android Open Source Project
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

package com.alexvanyo.composelife.ui.settings.entrypoints

import androidx.compose.runtime.Composable
import androidx.compose.ui.platform.LocalContext
import app.cash.sqldelight.async.coroutines.synchronous
import app.cash.sqldelight.driver.android.AndroidSqliteDriver
import coil3.ImageLoader
import com.alexvanyo.composelife.clock.di.ClockProvider
import com.alexvanyo.composelife.data.PatternCollectionRepositoryImpl
import com.alexvanyo.composelife.data.di.PatternCollectionRepositoryProvider
import com.alexvanyo.composelife.database.CellState
import com.alexvanyo.composelife.database.CellStateIdAdapter
import com.alexvanyo.composelife.database.ComposeLifeDatabase
import com.alexvanyo.composelife.database.InstantAdapter
import com.alexvanyo.composelife.database.PatternCollectionIdAdapter
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.dispatchers.DefaultComposeLifeDispatchers
import com.alexvanyo.composelife.imageloader.di.ImageLoaderProvider
import com.alexvanyo.composelife.logging.Logger
import com.alexvanyo.composelife.logging.NoOpLogger
import com.alexvanyo.composelife.model.CellStateParser
import com.alexvanyo.composelife.model.FlexibleCellStateSerializer
import com.alexvanyo.composelife.model.di.CellStateParserProvider
import com.alexvanyo.composelife.preferences.CurrentShape
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferences
import com.alexvanyo.composelife.preferences.TestComposeLifePreferences
import com.alexvanyo.composelife.preferences.currentShape
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.di.LoadedComposeLifePreferencesProvider
import com.alexvanyo.composelife.ui.cells.CellWindowInjectEntryPoint
import com.alexvanyo.composelife.ui.cells.CellWindowLocalEntryPoint
import com.alexvanyo.composelife.ui.cells.CellsFetcher
import com.alexvanyo.composelife.ui.cells.CellsKeyer
import com.alexvanyo.composelife.ui.cells.InteractableCellsLocalEntryPoint
import com.alexvanyo.composelife.ui.cells.NonInteractableCellsLocalEntryPoint
import com.alexvanyo.composelife.ui.settings.AlgorithmImplementationUiInjectEntryPoint
import com.alexvanyo.composelife.ui.settings.AlgorithmImplementationUiLocalEntryPoint
import com.alexvanyo.composelife.ui.settings.CellShapeConfigUiInjectEntryPoint
import com.alexvanyo.composelife.ui.settings.CellShapeConfigUiLocalEntryPoint
import com.alexvanyo.composelife.ui.settings.CellStatePreviewUiInjectEntryPoint
import com.alexvanyo.composelife.ui.settings.CellStatePreviewUiLocalEntryPoint
import com.alexvanyo.composelife.ui.settings.DarkThemeConfigUiInjectEntryPoint
import com.alexvanyo.composelife.ui.settings.DarkThemeConfigUiLocalEntryPoint
import com.alexvanyo.composelife.ui.settings.DisableAGSLUiInjectEntryPoint
import com.alexvanyo.composelife.ui.settings.DisableAGSLUiLocalEntryPoint
import com.alexvanyo.composelife.ui.settings.DisableOpenGLUiInjectEntryPoint
import com.alexvanyo.composelife.ui.settings.DisableOpenGLUiLocalEntryPoint
import com.alexvanyo.composelife.ui.settings.EnableClipboardWatchingUiInjectEntryPoint
import com.alexvanyo.composelife.ui.settings.EnableClipboardWatchingUiLocalEntryPoint
import com.alexvanyo.composelife.ui.settings.EnableWindowShapeClippingUiInjectEntryPoint
import com.alexvanyo.composelife.ui.settings.EnableWindowShapeClippingUiLocalEntryPoint
import com.alexvanyo.composelife.ui.settings.FullscreenSettingsDetailPaneInjectEntryPoint
import com.alexvanyo.composelife.ui.settings.FullscreenSettingsDetailPaneLocalEntryPoint
import com.alexvanyo.composelife.ui.settings.InlineSettingsPaneInjectEntryPoint
import com.alexvanyo.composelife.ui.settings.InlineSettingsPaneLocalEntryPoint
import com.alexvanyo.composelife.ui.settings.PatternCollectionsUiInjectEntryPoint
import com.alexvanyo.composelife.ui.settings.PatternCollectionsUiLocalEntryPoint
import com.alexvanyo.composelife.ui.settings.SettingUiInjectEntryPoint
import com.alexvanyo.composelife.ui.settings.SettingUiLocalEntryPoint
import io.ktor.client.HttpClient
import io.ktor.client.engine.mock.MockEngine
import okio.FileSystem
import okio.Path.Companion.toPath
import okio.fakefilesystem.FakeFileSystem
import kotlin.time.Clock

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
    DarkThemeConfigUiInjectEntryPoint,
    DarkThemeConfigUiLocalEntryPoint,
    DisableAGSLUiInjectEntryPoint,
    DisableAGSLUiLocalEntryPoint,
    DisableOpenGLUiInjectEntryPoint,
    DisableOpenGLUiLocalEntryPoint,
    EnableClipboardWatchingUiInjectEntryPoint,
    EnableClipboardWatchingUiLocalEntryPoint,
    EnableWindowShapeClippingUiInjectEntryPoint,
    EnableWindowShapeClippingUiLocalEntryPoint,
    FullscreenSettingsDetailPaneInjectEntryPoint,
    FullscreenSettingsDetailPaneLocalEntryPoint,
    InlineSettingsPaneInjectEntryPoint,
    InlineSettingsPaneLocalEntryPoint,
    InteractableCellsLocalEntryPoint,
    NonInteractableCellsLocalEntryPoint,
    PatternCollectionsUiInjectEntryPoint,
    PatternCollectionsUiLocalEntryPoint,
    SettingUiInjectEntryPoint,
    SettingUiLocalEntryPoint,
    ComposeLifePreferencesProvider

/**
 * Provides fake implementations for the entry points passed to [content] as context receivers.
 *
 * This is useful for providing dependencies to previews where the full dependency graph isn't available.
 */
@Suppress("LongParameterList", "LongMethod")
@Composable
internal fun WithPreviewDependencies(
    dispatchers: ComposeLifeDispatchers = DefaultComposeLifeDispatchers(),
    loadedComposeLifePreferences: LoadedComposeLifePreferences = LoadedComposeLifePreferences.Defaults,
    clock: Clock = Clock.System,
    cellStateParser: CellStateParser = CellStateParser(
        flexibleCellStateSerializer = FlexibleCellStateSerializer(
            dispatchers = dispatchers,
        ),
        dispatchers = dispatchers,
        context = LocalContext.current,
    ),
    logger: Logger = NoOpLogger,
    fileSystem: FileSystem = FakeFileSystem(
        clock = clock,
    ),
    content: @Composable context(PreviewEntryPoint) () -> Unit,
) {
    val driver = AndroidSqliteDriver(
        schema = ComposeLifeDatabase.Schema.synchronous(),
        context = LocalContext.current,
        name = null,
    )
    val composeLifeDatabase = ComposeLifeDatabase(
        driver = driver,
        cellStateAdapter = CellState.Adapter(
            idAdapter = CellStateIdAdapter(),
            patternCollectionIdAdapter = PatternCollectionIdAdapter(),
        ),
        patternCollectionAdapter = com.alexvanyo.composelife.database.PatternCollection.Adapter(
            idAdapter = PatternCollectionIdAdapter(),
            lastSuccessfulSynchronizationTimestampAdapter = InstantAdapter(),
            lastUnsuccessfulSynchronizationTimestampAdapter = InstantAdapter(),
        ),
    )
    val cellStateQueries = composeLifeDatabase.cellStateQueries
    val patternCollectionQueries = composeLifeDatabase.patternCollectionQueries

    val composeLifePreferences = TestComposeLifePreferences(
        algorithmChoice = loadedComposeLifePreferences.algorithmChoice,
        currentShapeType = loadedComposeLifePreferences.currentShape.type,
        roundRectangleConfig = when (loadedComposeLifePreferences.currentShape) {
            is CurrentShape.RoundRectangle -> loadedComposeLifePreferences.currentShape as CurrentShape.RoundRectangle
        },
        darkThemeConfig = loadedComposeLifePreferences.darkThemeConfig,
        disableAGSL = loadedComposeLifePreferences.disableAGSL,
        disableOpenGL = loadedComposeLifePreferences.disableOpenGL,
    )

    val preferencesProvider = object : ComposeLifePreferencesProvider {
        override val composeLifePreferences = composeLifePreferences
    }
    val loadedPreferencesProvider = object : LoadedComposeLifePreferencesProvider {
        override val preferences: LoadedComposeLifePreferences = loadedComposeLifePreferences
    }
    val cellStateParserProvider = object : CellStateParserProvider {
        override val cellStateParser = cellStateParser
    }
    val imageLoaderProvider = object : ImageLoaderProvider {
        override val imageLoader = ImageLoader.Builder(LocalContext.current)
            .components {
                add(CellsFetcher.Factory())
                add(CellsKeyer())
            }
            .build()
    }
    val clockProvider = object : ClockProvider {
        override val clock: Clock = clock
    }
    val patternCollectionRepositoryProvider = object : PatternCollectionRepositoryProvider {
        override val patternCollectionRepository = PatternCollectionRepositoryImpl(
            dispatchers = dispatchers,
            cellStateQueries = cellStateQueries,
            patternCollectionQueries = patternCollectionQueries,
            fileSystem = fileSystem,
            httpClient = lazy { HttpClient(MockEngine) },
            logger = logger,
            clock = clock,
            persistedDataPath = lazy { "persistedDataPath".toPath() },
        )
    }

    val entryPoint = object :
        PreviewEntryPoint,
        ComposeLifePreferencesProvider by preferencesProvider,
        LoadedComposeLifePreferencesProvider by loadedPreferencesProvider,
        CellStateParserProvider by cellStateParserProvider,
        ImageLoaderProvider by imageLoaderProvider,
        PatternCollectionRepositoryProvider by patternCollectionRepositoryProvider,
        ClockProvider by clockProvider {}

    content(entryPoint)
}
