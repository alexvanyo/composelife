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

package com.alexvanyo.composelife.ui.cells

import androidx.compose.foundation.Canvas
import androidx.compose.runtime.Composable
import androidx.compose.runtime.Immutable
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.unit.Dp
import coil3.ImageLoader
import com.alexvanyo.composelife.model.CellWindow
import com.alexvanyo.composelife.model.GameOfLifeState
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferences
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferencesHolder
import dev.zacsweers.metro.Assisted
import dev.zacsweers.metro.Inject

// region templated-ctx
context(ctx: NonInteractableCellsCtxClass)
@Composable
@Suppress("LongParameterList", "DEPRECATION")
fun NonInteractableCells(
    gameOfLifeState: GameOfLifeState,
    scaledCellDpSize: Dp,
    cellWindow: CellWindow,
    pixelOffsetFromCenter: Offset,
    isThumbnail: Boolean,
    modifier: Modifier = Modifier,
    inOverlay: Boolean = false,
) = ctx(gameOfLifeState, scaledCellDpSize, cellWindow, pixelOffsetFromCenter, isThumbnail, modifier, inOverlay)
// endregion templated-ctx

/**
 * A fixed size composable that displays a specific [cellWindow] into the given [GameOfLifeState].
 *
 * The [GameOfLifeState] is not interactable, so for efficiency the cell window is represented
 * by a single [Canvas], where each cell is drawn individually.
 */
context(
    imageLoader: ImageLoader,
preferencesHolder: LoadedComposeLifePreferencesHolder,
)
@Composable
@Inject
@Suppress("LongParameterList")
internal fun NonInteractableCellsCtx(
    @Assisted gameOfLifeState: GameOfLifeState,
    @Assisted scaledCellDpSize: Dp,
    @Assisted cellWindow: CellWindow,
    @Assisted pixelOffsetFromCenter: Offset,
    @Assisted isThumbnail: Boolean,
    @Assisted modifier: Modifier,
    @Assisted inOverlay: Boolean,
) {
    NonInteractableCellsImpl(
        gameOfLifeState,
        scaledCellDpSize,
        cellWindow,
        pixelOffsetFromCenter,
        isThumbnail,
        modifier,
        inOverlay,
    )
}

/**
 * A fixed size composable that displays a specific [cellWindow] into the given [GameOfLifeState].
 *
 * The [GameOfLifeState] is not interactable, so for efficiency the cell window is represented
 * by a single [Canvas], where each cell is drawn individually.
 */
context(
    imageLoader: ImageLoader,
preferencesHolder: LoadedComposeLifePreferencesHolder,
)
@Composable
@Suppress("LongParameterList")
internal expect fun NonInteractableCellsImpl(
    gameOfLifeState: GameOfLifeState,
    scaledCellDpSize: Dp,
    cellWindow: CellWindow,
    pixelOffsetFromCenter: Offset,
    isThumbnail: Boolean,
    modifier: Modifier,
    inOverlay: Boolean,
)

@Composable
expect fun isSharedElementForCellsSupported(
    preferences: LoadedComposeLifePreferences,
    isThumbnail: Boolean,
): Boolean
