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

package com.alexvanyo.composelife.ui

import androidx.compose.animation.Crossfade
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
import com.alexvanyo.composelife.data.di.CellStateRepositoryProvider
import com.alexvanyo.composelife.data.model.CellStateMetadata
import com.alexvanyo.composelife.data.model.SaveableCellState
import com.alexvanyo.composelife.model.rememberTemporalGameOfLifeState
import com.alexvanyo.composelife.model.rememberTemporalGameOfLifeStateMutator
import com.alexvanyo.composelife.model.toCellState
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferences
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.di.LoadedComposeLifePreferencesProvider
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.ui.component.GameOfLifeProgressIndicator
import com.alexvanyo.composelife.ui.component.GameOfLifeProgressIndicatorHiltEntryPoint
import com.alexvanyo.composelife.ui.component.GameOfLifeProgressIndicatorLocalEntryPoint
import com.alexvanyo.composelife.ui.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.theme.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.SizePreviews
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
    InteractiveCellUniverseHiltEntryPoint

context(ComposeLifeAppHiltEntryPoint)
@Suppress("LongMethod")
@Composable
fun ComposeLifeApp(
    windowSizeClass: WindowSizeClass,
) {
    val loadedPreferencesState = composeLifePreferences.loadedPreferencesState

    Surface(modifier = Modifier.fillMaxSize()) {
        Box(
            contentAlignment = Alignment.Center,
        ) {
            when (loadedPreferencesState) {
                is ResourceState.Failure -> Unit
                ResourceState.Loading -> {
                    CircularProgressIndicator()
                }
                is ResourceState.Success -> {
                    val currentLoadedPreferences by rememberUpdatedState(loadedPreferencesState.value)

                    val loadedPreferencesProvider = remember {
                        object : LoadedComposeLifePreferencesProvider {
                            override val preferences: LoadedComposeLifePreferences
                                get() = currentLoadedPreferences
                        }
                    }

                    val localEntryPoint = remember {
                        object :
                            InteractiveCellUniverseLocalEntryPoint,
                            GameOfLifeProgressIndicatorLocalEntryPoint,
                            LoadedComposeLifePreferencesProvider by loadedPreferencesProvider {}
                    }
                    with(localEntryPoint) {
                        var initialSaveableCellState by remember { mutableStateOf<SaveableCellState?>(null) }

                        if (initialSaveableCellState == null) {
                            LaunchedEffect(cellStateRepository) {
                                initialSaveableCellState = cellStateRepository.getAutosavedCellState()
                                    ?: SaveableCellState(
                                        gosperGliderGun,
                                        CellStateMetadata(null, null, null, 0, false),
                                    )
                            }
                        }

                        Crossfade(initialSaveableCellState) { targetSaveableCellState ->
                            if (targetSaveableCellState == null) {
                                Box(
                                    contentAlignment = Alignment.Center,
                                    modifier = Modifier.fillMaxSize(),
                                ) {
                                    GameOfLifeProgressIndicator()
                                }
                            } else {
                                val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                                    seedCellState = targetSaveableCellState.cellState,
                                    isRunning = false,
                                )

                                var isViewportTracking by rememberSaveable { mutableStateOf(false) }

                                val temporalGameOfLifeStateMutator = rememberTemporalGameOfLifeStateMutator(
                                    temporalGameOfLifeState = temporalGameOfLifeState,
                                    gameOfLifeAlgorithm = gameOfLifeAlgorithm,
                                    dispatchers = dispatchers,
                                )

                                LaunchedEffect(temporalGameOfLifeStateMutator) {
                                    temporalGameOfLifeStateMutator.update()
                                }

                                var cellStateMetadataId by remember {
                                    mutableStateOf(targetSaveableCellState.cellStateMetadata.id)
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
                                                        name = targetSaveableCellState.cellStateMetadata.name,
                                                        description = targetSaveableCellState
                                                            .cellStateMetadata
                                                            .description,
                                                        generation = targetSaveableCellState
                                                            .cellStateMetadata
                                                            .generation,
                                                        wasAutosaved = targetSaveableCellState
                                                            .cellStateMetadata
                                                            .wasAutosaved,
                                                    ),
                                                ),
                                            )
                                        }
                                        .collect()
                                }

                                InteractiveCellUniverse(
                                    temporalGameOfLifeState = temporalGameOfLifeState,
                                    isViewportTracking = isViewportTracking,
                                    setIsViewportTracking = { isViewportTracking = it },
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
@SizePreviews
@Composable
fun InteractiveCellUniversePreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            BoxWithConstraints {
                val size = DpSize(maxWidth, maxHeight)
                Surface {
                    InteractiveCellUniverse(
                        temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                            seedCellState = gosperGliderGun,
                            isRunning = false,
                        ),
                        isViewportTracking = false,
                        setIsViewportTracking = {},
                        windowSizeClass = WindowSizeClass.calculateFromSize(size),
                    )
                }
            }
        }
    }
}
