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

package com.alexvanyo.composelife.ui.action.settings

import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.layout.size
import androidx.compose.material3.Surface
import androidx.compose.runtime.Composable
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.model.GameOfLifeState
import com.alexvanyo.composelife.model.toCellState
import com.alexvanyo.composelife.preferences.CurrentShape
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.resourcestate.combine
import com.alexvanyo.composelife.ui.cells.CellWindowState
import com.alexvanyo.composelife.ui.cells.ImmutableCellWindow
import com.alexvanyo.composelife.ui.component.GameOfLifeProgressIndicator
import com.alexvanyo.composelife.ui.component.GameOfLifeProgressIndicatorEntryPoint
import com.alexvanyo.composelife.ui.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.theme.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.ThemePreviews
import dagger.hilt.EntryPoint
import dagger.hilt.InstallIn
import dagger.hilt.android.components.ActivityComponent

@EntryPoint
@InstallIn(ActivityComponent::class)
interface CellStatePreviewUiEntryPoint :
    GameOfLifeProgressIndicatorEntryPoint,
    ComposeLifePreferencesProvider

context(CellStatePreviewUiEntryPoint)
@Composable
fun CellStatePreviewUi(
    modifier: Modifier = Modifier,
) {
    CellStatePreviewUi(
        currentShapeState = composeLifePreferences.currentShapeState,
        disableAGSLState = composeLifePreferences.disableAGSLState,
        disableOpenGLState = composeLifePreferences.disableOpenGLState,
        modifier = modifier,
    )
}

context(CellStatePreviewUiEntryPoint)
@Suppress("LongMethod")
@Composable
fun CellStatePreviewUi(
    currentShapeState: ResourceState<CurrentShape>,
    disableAGSLState: ResourceState<Boolean>,
    disableOpenGLState: ResourceState<Boolean>,
    modifier: Modifier = Modifier,
) {
    Box(
        modifier = modifier.fillMaxWidth(),
        contentAlignment = Alignment.Center,
    ) {
        when (val combinedState = combine(currentShapeState, disableAGSLState, disableOpenGLState, ::Triple)) {
            ResourceState.Loading, is ResourceState.Failure -> {
                GameOfLifeProgressIndicator()
            }
            is ResourceState.Success -> {
                val (currentShape, disableAGSL, disableOpenGL) = combinedState.value

                ImmutableCellWindow(
                    gameOfLifeState = GameOfLifeState(
                        """
                        |.....
                        |..O..
                        |...O.
                        |.OOO.
                        |.....
                        """.toCellState(),
                    ),
                    shape = currentShape,
                    disableAGSL = disableAGSL,
                    disableOpenGL = disableOpenGL,
                    cellWindowState = CellWindowState(
                        offset = Offset(2f, 2f),
                    ),
                    cellDpSize = 96.dp / 5,
                    modifier = Modifier.size(96.dp),
                )
            }
        }
    }
}

@ThemePreviews
@Composable
fun CellStatePreviewUiLoadingPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            Surface {
                CellStatePreviewUi(
                    currentShapeState = ResourceState.Loading,
                    disableAGSLState = ResourceState.Loading,
                    disableOpenGLState = ResourceState.Loading,
                )
            }
        }
    }
}

@ThemePreviews
@Composable
fun CellStatePreviewUiRoundRectanglePreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            Surface {
                CellStatePreviewUi(
                    currentShapeState = ResourceState.Success(
                        CurrentShape.RoundRectangle(
                            sizeFraction = 0.8f,
                            cornerFraction = 0.4f,
                        ),
                    ),
                    disableAGSLState = ResourceState.Success(false),
                    disableOpenGLState = ResourceState.Success(false),
                )
            }
        }
    }
}
