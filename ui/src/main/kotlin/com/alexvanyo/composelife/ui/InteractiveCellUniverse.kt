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

import androidx.compose.foundation.layout.Box
import androidx.compose.material3.Surface
import androidx.compose.material3.windowsizeclass.WindowSizeClass
import androidx.compose.runtime.Composable
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.platform.testTag
import com.alexvanyo.composelife.model.TemporalGameOfLifeState
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.ui.cells.CellWindowState
import com.alexvanyo.composelife.ui.cells.MutableCellWindow
import com.alexvanyo.composelife.ui.cells.rememberCellWindowState
import com.alexvanyo.composelife.ui.component.GameOfLifeProgressIndicator
import dagger.hilt.EntryPoint
import dagger.hilt.InstallIn
import dagger.hilt.android.components.ActivityComponent

@EntryPoint
@InstallIn(ActivityComponent::class)
interface InteractiveCellUniverseEntryPoint : InteractiveCellUniverseOverlayEntryPoint

/**
 * An interactive cell universe displaying the given [temporalGameOfLifeState] and the controls for adjusting how it
 * evolves.
 */
context(InteractiveCellUniverseEntryPoint)
@Composable
fun InteractiveCellUniverse(
    temporalGameOfLifeState: TemporalGameOfLifeState,
    windowSizeClass: WindowSizeClass,
    modifier: Modifier = Modifier,
    cellWindowState: CellWindowState = rememberCellWindowState(),
) {
    val currentShapeState = composeLifePreferences.currentShapeState

    Surface(modifier = modifier) {
        Box(
            contentAlignment = Alignment.Center,
        ) {
            when (currentShapeState) {
                is ResourceState.Failure -> Unit
                ResourceState.Loading -> {
                    GameOfLifeProgressIndicator()
                }
                is ResourceState.Success -> {
                    MutableCellWindow(
                        gameOfLifeState = temporalGameOfLifeState,
                        cellWindowState = cellWindowState,
                        shape = currentShapeState.value,
                        modifier = Modifier.testTag("MutableCellWindow"),
                    )
                }
            }

            InteractiveCellUniverseOverlay(
                temporalGameOfLifeState = temporalGameOfLifeState,
                cellWindowState = cellWindowState,
                windowSizeClass = windowSizeClass,
            )
        }
    }
}
