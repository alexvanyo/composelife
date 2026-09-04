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

import androidx.compose.runtime.Composable
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.unit.Dp
import coil3.ImageLoader
import com.alexvanyo.composelife.di.InjectContext
import com.alexvanyo.composelife.model.CellWindow
import com.alexvanyo.composelife.model.GameOfLifeState
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferences
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferencesHolder
import dev.zacsweers.metro.Assisted
import dev.zacsweers.metro.Inject

@InjectContext
@Inject
@Suppress("LongParameterList")
@Composable
context(
    imageLoader: ImageLoader,
    preferencesHolder: LoadedComposeLifePreferencesHolder,
)
fun NonInteractableCells(
    @Assisted gameOfLifeState: GameOfLifeState,
    @Assisted scaledCellDpSize: Dp,
    @Assisted cellWindow: CellWindow,
    @Assisted pixelOffsetFromCenter: Offset,
    @Assisted isThumbnail: Boolean,
    @Assisted modifier: Modifier = Modifier,
    @Assisted inOverlay: Boolean = false,
) {
    PlatformNonInteractableCells(
        gameOfLifeState = gameOfLifeState,
        scaledCellDpSize = scaledCellDpSize,
        cellWindow = cellWindow,
        pixelOffsetFromCenter = pixelOffsetFromCenter,
        isThumbnail = isThumbnail,
        modifier = modifier,
        inOverlay = inOverlay,
    )
}

@Suppress("LongParameterList")
@Composable
context(
    imageLoader: ImageLoader,
    preferencesHolder: LoadedComposeLifePreferencesHolder,
)
internal expect fun PlatformNonInteractableCells(
    gameOfLifeState: GameOfLifeState,
    scaledCellDpSize: Dp,
    cellWindow: CellWindow,
    pixelOffsetFromCenter: Offset,
    isThumbnail: Boolean,
    modifier: Modifier = Modifier,
    inOverlay: Boolean = false,
)

@Composable
expect fun isSharedElementForCellsSupported(preferences: LoadedComposeLifePreferences, isThumbnail: Boolean): Boolean
