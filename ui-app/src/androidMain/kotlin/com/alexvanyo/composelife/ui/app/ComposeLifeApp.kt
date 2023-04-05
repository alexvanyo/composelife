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

package com.alexvanyo.composelife.ui.app

import androidx.activity.compose.ReportDrawn
import androidx.compose.animation.Crossfade
import androidx.compose.animation.ExperimentalAnimationApi
import androidx.compose.animation.core.updateTransition
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.BoxWithConstraints
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.material3.CircularProgressIndicator
import androidx.compose.material3.Surface
import androidx.compose.material3.windowsizeclass.ExperimentalMaterial3WindowSizeClassApi
import androidx.compose.material3.windowsizeclass.WindowSizeClass
import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import androidx.compose.runtime.snapshotFlow
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.unit.DpSize
import com.alexvanyo.composelife.algorithm.di.GameOfLifeAlgorithmProvider
import com.alexvanyo.composelife.clock.di.ClockProvider
import com.alexvanyo.composelife.data.di.CellStateRepositoryProvider
import com.alexvanyo.composelife.data.model.CellStateMetadata
import com.alexvanyo.composelife.data.model.SaveableCellState
import com.alexvanyo.composelife.dispatchers.di.ComposeLifeDispatchersProvider
import com.alexvanyo.composelife.model.TemporalGameOfLifeState
import com.alexvanyo.composelife.model.rememberTemporalGameOfLifeState
import com.alexvanyo.composelife.model.rememberTemporalGameOfLifeStateMutator
import com.alexvanyo.composelife.model.toCellState
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferences
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.di.LoadedComposeLifePreferencesProvider
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.ui.app.component.GameOfLifeProgressIndicator
import com.alexvanyo.composelife.ui.app.component.GameOfLifeProgressIndicatorHiltEntryPoint
import com.alexvanyo.composelife.ui.app.component.GameOfLifeProgressIndicatorLocalEntryPoint
import com.alexvanyo.composelife.ui.app.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.app.theme.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.MobileDevicePreviews
import dagger.hilt.EntryPoint
import dagger.hilt.InstallIn
import dagger.hilt.android.components.ActivityComponent
import kotlinx.coroutines.delay
import kotlinx.coroutines.flow.collect
import kotlinx.coroutines.flow.conflate
import kotlinx.coroutines.flow.onEach
import kotlinx.coroutines.flow.transform
import kotlin.time.Duration.Companion.seconds

@EntryPoint
@InstallIn(ActivityComponent::class)
interface ComposeLifeAppHiltEntryPoint :
    ComposeLifePreferencesProvider,
    CellStateRepositoryProvider,
    GameOfLifeProgressIndicatorHiltEntryPoint,
    InteractiveCellUniverseHiltEntryPoint,
    ClockProvider

context(ComposeLifeAppHiltEntryPoint)
@OptIn(ExperimentalAnimationApi::class)
@Composable
fun ComposeLifeApp(
    windowSizeClass: WindowSizeClass,
    modifier: Modifier = Modifier,
    composeLifeAppState: ComposeLifeAppState = rememberComposeLifeAppState(),
) {
    Surface(modifier = modifier.fillMaxSize()) {
        val transition = updateTransition(composeLifeAppState, "ComposeLifeAppState Crossfade")
        transition.Crossfade(
            contentKey = {
                when (it) {
                    ComposeLifeAppState.ErrorLoadingPreferences -> 0
                    is ComposeLifeAppState.LoadedPreferences.LoadedCellState -> 1
                    is ComposeLifeAppState.LoadedPreferences.LoadingCellState -> 2
                    ComposeLifeAppState.LoadingPreferences -> 3
                }
            },
        ) { targetComposeLifeAppState ->
            when (targetComposeLifeAppState) {
                ComposeLifeAppState.ErrorLoadingPreferences -> Unit
                ComposeLifeAppState.LoadingPreferences -> {
                    Box(
                        contentAlignment = Alignment.Center,
                        modifier = Modifier.fillMaxSize(),
                    ) {
                        CircularProgressIndicator()
                    }
                }
                is ComposeLifeAppState.LoadedPreferences -> {
                    val localEntryPoint = remember {
                        object :
                            InteractiveCellUniverseLocalEntryPoint,
                            GameOfLifeProgressIndicatorLocalEntryPoint,
                            LoadedComposeLifePreferencesProvider by targetComposeLifeAppState {}
                    }

                    with(localEntryPoint) {
                        when (targetComposeLifeAppState) {
                            is ComposeLifeAppState.LoadedPreferences.LoadingCellState -> {
                                Box(
                                    contentAlignment = Alignment.Center,
                                    modifier = Modifier.fillMaxSize(),
                                ) {
                                    GameOfLifeProgressIndicator()
                                }
                            }
                            is ComposeLifeAppState.LoadedPreferences.LoadedCellState -> {
                                ReportDrawn()

                                InteractiveCellUniverse(
                                    temporalGameOfLifeState = targetComposeLifeAppState.temporalGameOfLifeState,
                                    isViewportTracking = targetComposeLifeAppState.isViewportTracking,
                                    setIsViewportTracking = { targetComposeLifeAppState.isViewportTracking = it },
                                    windowSizeClass = windowSizeClass,
                                )
                            }
                        }
                    }
                }
            }
        }
    }
}

context(
    ComposeLifePreferencesProvider, CellStateRepositoryProvider, GameOfLifeAlgorithmProvider,
    ComposeLifeDispatchersProvider, ClockProvider
)
@Suppress("LongMethod")
@Composable
fun rememberComposeLifeAppState(): ComposeLifeAppState {
    val loadedPreferencesState = composeLifePreferences.loadedPreferencesState

    var initialSaveableCellState by remember { mutableStateOf<SaveableCellState?>(null) }
    val currentInitialSaveableCellState = initialSaveableCellState

    if (currentInitialSaveableCellState == null) {
        LaunchedEffect(cellStateRepository) {
            initialSaveableCellState = cellStateRepository.getAutosavedCellState()
                ?: SaveableCellState(
                    gosperGliderGun,
                    CellStateMetadata(null, null, null, 0, false),
                )
        }
    }

    return when (loadedPreferencesState) {
        is ResourceState.Failure -> ComposeLifeAppState.ErrorLoadingPreferences
        ResourceState.Loading -> ComposeLifeAppState.LoadingPreferences
        is ResourceState.Success -> {
            val currentLoadedPreferences by rememberUpdatedState(loadedPreferencesState.value)

            if (currentInitialSaveableCellState == null) {
                remember {
                    object : ComposeLifeAppState.LoadedPreferences.LoadingCellState {
                        override val preferences get() = currentLoadedPreferences
                    }
                }
            } else {
                val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                    seedCellState = currentInitialSaveableCellState.cellState,
                    isRunning = false,
                )

                var isViewportTracking by rememberSaveable { mutableStateOf(false) }

                val temporalGameOfLifeStateMutator = rememberTemporalGameOfLifeStateMutator(
                    temporalGameOfLifeState = temporalGameOfLifeState,
                    gameOfLifeAlgorithm = gameOfLifeAlgorithm,
                    dispatchers = dispatchers,
                    clock = clock,
                )

                LaunchedEffect(temporalGameOfLifeStateMutator) {
                    temporalGameOfLifeStateMutator.update()
                }

                var cellStateMetadataId by remember {
                    mutableStateOf(currentInitialSaveableCellState.cellStateMetadata.id)
                }

                LaunchedEffect(temporalGameOfLifeState) {
                    snapshotFlow { temporalGameOfLifeState.cellState }
                        .conflate()
                        .transform {
                            emit(it)
                            delay(5.seconds)
                        }
                        .onEach { cellState ->
                            cellStateMetadataId = cellStateRepository.autosaveCellState(
                                saveableCellState = SaveableCellState(
                                    cellState = cellState,
                                    cellStateMetadata = CellStateMetadata(
                                        id = cellStateMetadataId,
                                        name = currentInitialSaveableCellState.cellStateMetadata.name,
                                        description = currentInitialSaveableCellState
                                            .cellStateMetadata
                                            .description,
                                        generation = currentInitialSaveableCellState
                                            .cellStateMetadata
                                            .generation,
                                        wasAutosaved = currentInitialSaveableCellState
                                            .cellStateMetadata
                                            .wasAutosaved,
                                    ),
                                ),
                            )
                        }
                        .collect()
                }

                remember(temporalGameOfLifeState) {
                    object : ComposeLifeAppState.LoadedPreferences.LoadedCellState {
                        override val preferences: LoadedComposeLifePreferences get() = currentLoadedPreferences
                        override val temporalGameOfLifeState = temporalGameOfLifeState
                        override var isViewportTracking
                            get() = isViewportTracking
                            set(value) {
                                isViewportTracking = value
                            }
                    }
                }
            }
        }
    }
}

sealed interface ComposeLifeAppState {
    /**
     * The user's preferences are loading.
     */
    object LoadingPreferences : ComposeLifeAppState

    /**
     * There was an error loading the user's preferences.
     */
    object ErrorLoadingPreferences : ComposeLifeAppState

    /**
     * The user's preferences are loaded, so the state can be a [LoadedComposeLifePreferencesProvider].
     */
    sealed interface LoadedPreferences : ComposeLifeAppState, LoadedComposeLifePreferencesProvider {

        /**
         * The initial cell state is loading
         */
        interface LoadingCellState : LoadedPreferences

        /**
         * The cell state is loaded
         */
        interface LoadedCellState : LoadedPreferences {
            val temporalGameOfLifeState: TemporalGameOfLifeState
            var isViewportTracking: Boolean
        }
    }
}

private val gosperGliderGun = """
    |........................O...........
    |......................O.O...........
    |............OO......OO............OO
    |...........O...O....OO............OO
    |OO........O.....O...OO..............
    |OO........O...O.OO....O.O...........
    |..........O.....O.......O...........
    |...........O...O....................
    |............OO......................
""".toCellState()

@OptIn(ExperimentalMaterial3WindowSizeClassApi::class)
@MobileDevicePreviews
@Composable
fun LoadingPreferencesComposeLifeAppPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            BoxWithConstraints {
                val size = DpSize(maxWidth, maxHeight)
                ComposeLifeApp(
                    windowSizeClass = WindowSizeClass.calculateFromSize(size),
                    composeLifeAppState = ComposeLifeAppState.LoadingPreferences,
                )
            }
        }
    }
}

@OptIn(ExperimentalMaterial3WindowSizeClassApi::class)
@MobileDevicePreviews
@Composable
fun LoadingCellStateComposeLifeAppPreview() {
    WithPreviewDependencies {
        val preferences = preferences
        ComposeLifeTheme {
            BoxWithConstraints {
                val size = DpSize(maxWidth, maxHeight)
                ComposeLifeApp(
                    windowSizeClass = WindowSizeClass.calculateFromSize(size),
                    composeLifeAppState = object : ComposeLifeAppState.LoadedPreferences.LoadingCellState {
                        override val preferences = preferences
                    },
                )
            }
        }
    }
}

@OptIn(ExperimentalMaterial3WindowSizeClassApi::class)
@MobileDevicePreviews
@Composable
fun LoadedComposeLifeAppPreview() {
    WithPreviewDependencies {
        val preferences = preferences
        ComposeLifeTheme {
            BoxWithConstraints {
                val size = DpSize(maxWidth, maxHeight)
                val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                    seedCellState = gosperGliderGun,
                    isRunning = false,
                )
                ComposeLifeApp(
                    windowSizeClass = WindowSizeClass.calculateFromSize(size),
                    composeLifeAppState = object : ComposeLifeAppState.LoadedPreferences.LoadedCellState {
                        override val preferences = preferences
                        override val temporalGameOfLifeState = temporalGameOfLifeState
                        override var isViewportTracking = false
                    },
                )
            }
        }
    }
}
