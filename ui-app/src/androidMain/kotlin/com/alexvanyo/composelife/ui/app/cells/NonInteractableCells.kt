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

package com.alexvanyo.composelife.ui.app.cells

import android.os.Build
import androidx.compose.foundation.Canvas
import androidx.compose.foundation.layout.size
import androidx.compose.runtime.Composable
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.platform.LocalInspectionMode
import androidx.compose.ui.unit.Dp
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.model.GameOfLifeState
import com.alexvanyo.composelife.model.toCellState
import com.alexvanyo.composelife.preferences.di.LoadedComposeLifePreferencesProvider
import com.alexvanyo.composelife.ui.app.entrypoints.WithPreviewDependencies
import com.alexvanyo.composelife.ui.app.theme.ComposeLifeTheme
import com.alexvanyo.composelife.ui.util.ThemePreviews

interface NonInteractableCellsLocalEntryPoint :
    LoadedComposeLifePreferencesProvider

/**
 * A fixed size composable that displays a specific [cellWindow] into the given [GameOfLifeState].
 *
 * The [GameOfLifeState] is not interactable, so for efficiency the cell window is represented
 * by a single [Canvas], where each cell is drawn individually.
 */
context(NonInteractableCellsLocalEntryPoint)
@Composable
@Suppress("LongParameterList")
fun NonInteractableCells(
    gameOfLifeState: GameOfLifeState,
    scaledCellDpSize: Dp,
    cellWindow: IntRect,
    pixelOffsetFromCenter: Offset,
    modifier: Modifier = Modifier,
    inOverlay: Boolean = false,
) {
    if (!preferences.disableAGSL && Build.VERSION.SDK_INT >= 33 && Build.FINGERPRINT?.lowercase() != "robolectric") {
        AGSLNonInteractableCells(
            gameOfLifeState = gameOfLifeState,
            scaledCellDpSize = scaledCellDpSize,
            cellWindow = cellWindow,
            shape = preferences.currentShape,
            pixelOffsetFromCenter = pixelOffsetFromCenter,
            modifier = modifier,
        )
    } else if (!preferences.disableOpenGL && !LocalInspectionMode.current && openGLSupported()) {
        OpenGLNonInteractableCells(
            gameOfLifeState = gameOfLifeState,
            scaledCellDpSize = scaledCellDpSize,
            cellWindow = cellWindow,
            shape = preferences.currentShape,
            pixelOffsetFromCenter = pixelOffsetFromCenter,
            modifier = modifier,
            inOverlay = inOverlay,
        )
    } else {
        CanvasNonInteractableCells(
            gameOfLifeState = gameOfLifeState,
            scaledCellDpSize = scaledCellDpSize,
            cellWindow = cellWindow,
            shape = preferences.currentShape,
            pixelOffsetFromCenter = pixelOffsetFromCenter,
            modifier = modifier,
        )
    }
}

@ThemePreviews
@Composable
fun NonInteractableCellsPreview() {
    WithPreviewDependencies {
        ComposeLifeTheme {
            NonInteractableCells(
                gameOfLifeState = GameOfLifeState(
                    setOf(
                        0 to 0,
                        0 to 2,
                        0 to 4,
                        2 to 0,
                        2 to 2,
                        2 to 4,
                        4 to 0,
                        4 to 2,
                        4 to 4,
                    ).toCellState(),
                ),
                scaledCellDpSize = 32.dp,
                cellWindow = IntRect(
                    IntOffset(0, 0),
                    IntOffset(9, 9),
                ),
                pixelOffsetFromCenter = Offset.Zero,
                modifier = Modifier.size(300.dp),
            )
        }
    }
}
