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

package com.alexvanyo.composelife.ui.app.cells

import android.os.Build
import androidx.compose.runtime.Composable
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.platform.LocalInspectionMode
import androidx.compose.ui.unit.Dp
import com.alexvanyo.composelife.model.CellWindow
import com.alexvanyo.composelife.model.GameOfLifeState
import com.alexvanyo.composelife.preferences.currentShape
import com.alexvanyo.composelife.preferences.di.LoadedComposeLifePreferencesProvider

context(NonInteractableCellsLocalEntryPoint)

@Composable
@Suppress("LongParameterList")
actual fun NonInteractableCells(
    gameOfLifeState: GameOfLifeState,
    scaledCellDpSize: Dp,
    cellWindow: CellWindow,
    pixelOffsetFromCenter: Offset,
    modifier: Modifier,
    inOverlay: Boolean,
) {
    when (computeImplementationType()) {
        NonInteractableCellsImplementationType.AGSL -> {
            @Suppress("NewApi") // Checked by computeImplementationType
            AGSLNonInteractableCells(
                gameOfLifeState = gameOfLifeState,
                scaledCellDpSize = scaledCellDpSize,
                cellWindow = cellWindow,
                shape = preferences.currentShape,
                pixelOffsetFromCenter = pixelOffsetFromCenter,
                modifier = modifier,
            )
        }
        NonInteractableCellsImplementationType.Canvas -> {
            CanvasNonInteractableCells(
                gameOfLifeState = gameOfLifeState,
                scaledCellDpSize = scaledCellDpSize,
                cellWindow = cellWindow,
                shape = preferences.currentShape,
                pixelOffsetFromCenter = pixelOffsetFromCenter,
                modifier = modifier,
            )
        }
        NonInteractableCellsImplementationType.OpenGL -> {
            OpenGLNonInteractableCells(
                gameOfLifeState = gameOfLifeState,
                scaledCellDpSize = scaledCellDpSize,
                cellWindow = cellWindow,
                shape = preferences.currentShape,
                pixelOffsetFromCenter = pixelOffsetFromCenter,
                modifier = modifier,
                inOverlay = inOverlay,
            )
        }
    }
}

private sealed interface NonInteractableCellsImplementationType {
    data object AGSL : NonInteractableCellsImplementationType
    data object OpenGL : NonInteractableCellsImplementationType
    data object Canvas : NonInteractableCellsImplementationType
}

context(LoadedComposeLifePreferencesProvider)
@Composable
private fun computeImplementationType(): NonInteractableCellsImplementationType =
    when {
        !preferences.disableAGSL && Build.VERSION.SDK_INT >= 33 && Build.FINGERPRINT?.lowercase() != "robolectric" ->
            NonInteractableCellsImplementationType.AGSL
        !preferences.disableOpenGL && !LocalInspectionMode.current && openGLSupported() ->
            NonInteractableCellsImplementationType.OpenGL
        else ->
            NonInteractableCellsImplementationType.Canvas
    }

/**
 * Returns `true` is shared elements are supported by the resulting implementation of [NonInteractableCells].
 */
context(LoadedComposeLifePreferencesProvider)
@Composable
actual fun isSharedElementForCellsSupported(): Boolean =
    when (computeImplementationType()) {
        NonInteractableCellsImplementationType.AGSL,
        NonInteractableCellsImplementationType.Canvas,
        -> true
        NonInteractableCellsImplementationType.OpenGL -> false
    }
