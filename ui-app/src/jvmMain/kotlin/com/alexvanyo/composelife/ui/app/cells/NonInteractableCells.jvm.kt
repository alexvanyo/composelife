/*
 * Copyright 2023 The Android Open Source Project
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

import androidx.compose.runtime.Composable
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.unit.Dp
import com.alexvanyo.composelife.model.CellWindow
import com.alexvanyo.composelife.model.GameOfLifeState
import com.alexvanyo.composelife.preferences.currentShape

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
    if (!preferences.disableAGSL) {
        SKSLNonInteractableCells(
            gameOfLifeState = gameOfLifeState,
            scaledCellDpSize = scaledCellDpSize,
            cellWindow = cellWindow,
            shape = preferences.currentShape,
            pixelOffsetFromCenter = pixelOffsetFromCenter,
            modifier = modifier,
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
