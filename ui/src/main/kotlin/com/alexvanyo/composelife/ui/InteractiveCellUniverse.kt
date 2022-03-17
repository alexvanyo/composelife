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

package com.alexvanyo.composelife.ui

import androidx.compose.foundation.layout.Box
import androidx.compose.material3.CircularProgressIndicator
import androidx.compose.runtime.Composable
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.hilt.navigation.compose.hiltViewModel
import com.alexvanyo.composelife.model.TemporalGameOfLifeState
import com.alexvanyo.composelife.preferences.ComposeLifePreferences
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.ui.cells.CellWindowState
import com.alexvanyo.composelife.ui.cells.MutableCellWindow
import com.alexvanyo.composelife.ui.cells.rememberCellWindowState
import com.alexvanyo.composelife.ui.entrypoints.ComposeLifePreferencesEntryPoint

/**
 * An interactive cell universe displaying the given [temporalGameOfLifeState] and the controls for adjusting how it
 * evolves.
 */
@Composable
fun InteractiveCellUniverse(
    temporalGameOfLifeState: TemporalGameOfLifeState,
    modifier: Modifier = Modifier,
    cellWindowState: CellWindowState = rememberCellWindowState(),
    preferences: ComposeLifePreferences = hiltViewModel<ComposeLifePreferencesEntryPoint>().composeLifePreferences
) {
    val currentShapeState = preferences.currentShapeState

    Box(
        contentAlignment = Alignment.Center,
        modifier = modifier,
    ) {
        when (currentShapeState) {
            is ResourceState.Failure -> Unit
            ResourceState.Loading -> {
                CircularProgressIndicator()
            }
            is ResourceState.Success -> {
                MutableCellWindow(
                    gameOfLifeState = temporalGameOfLifeState,
                    cellWindowState = cellWindowState,
                    shape = currentShapeState.value
                )
            }
        }

        InteractiveCellUniverseOverlay(
            temporalGameOfLifeState = temporalGameOfLifeState,
            cellWindowState = cellWindowState
        )
    }
}
