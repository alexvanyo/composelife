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
import androidx.compose.material3.Surface
import androidx.compose.runtime.Composable
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import androidx.compose.ui.unit.IntSize
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.model.GameOfLifeState
import com.alexvanyo.composelife.model.toCellState
import com.alexvanyo.composelife.preferences.CurrentShape
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.ui.cells.NonInteractableCells
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
        modifier = modifier,
    )
}

context(CellStatePreviewUiEntryPoint)
@Suppress("LongMethod")
@Composable
fun CellStatePreviewUi(
    currentShapeState: ResourceState<CurrentShape>,
    modifier: Modifier = Modifier,
) {
    Box(
        modifier = modifier.fillMaxWidth(),
        contentAlignment = Alignment.Center,
    ) {
        when (currentShapeState) {
            ResourceState.Loading, is ResourceState.Failure -> {
                GameOfLifeProgressIndicator()
            }
            is ResourceState.Success -> {
                NonInteractableCells(
                    gameOfLifeState = GameOfLifeState(
                        """
                        |.....
                        |..O..
                        |...O.
                        |.OOO.
                        |.....
                        """.toCellState(),
                    ),
                    scaledCellDpSize = 96.dp / 5,
                    cellWindow = IntRect(IntOffset.Zero, IntSize(4, 4)),
                    shape = currentShapeState.value,
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
                )
            }
        }
    }
}
