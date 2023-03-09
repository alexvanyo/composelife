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

package com.alexvanyo.composelife.ui.app

import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.material3.windowsizeclass.WindowSizeClass
import androidx.compose.runtime.Composable
import androidx.compose.runtime.remember
import androidx.compose.ui.Modifier
import androidx.compose.ui.platform.testTag
import com.alexvanyo.composelife.model.TemporalGameOfLifeState
import com.alexvanyo.composelife.ui.app.cells.CellWindowLocalEntryPoint
import com.alexvanyo.composelife.ui.app.cells.MutableCellWindow
import com.alexvanyo.composelife.ui.app.cells.MutableCellWindowState
import com.alexvanyo.composelife.ui.app.cells.TrackingCellWindowState
import com.alexvanyo.composelife.ui.app.cells.ViewportInteractionConfig
import com.alexvanyo.composelife.ui.app.cells.rememberMutableCellWindowState
import com.alexvanyo.composelife.ui.app.cells.rememberTrackingCellWindowState
import dagger.hilt.EntryPoint
import dagger.hilt.InstallIn
import dagger.hilt.android.components.ActivityComponent

@EntryPoint
@InstallIn(ActivityComponent::class)
interface InteractiveCellUniverseHiltEntryPoint :
    InteractiveCellUniverseOverlayHiltEntryPoint

interface InteractiveCellUniverseLocalEntryPoint :
    CellWindowLocalEntryPoint,
    InteractiveCellUniverseOverlayLocalEntryPoint

/**
 * An interactive cell universe displaying the given [temporalGameOfLifeState] and the controls for adjusting how it
 * evolves.
 */
context(InteractiveCellUniverseHiltEntryPoint, InteractiveCellUniverseLocalEntryPoint)
@Suppress("LongParameterList")
@Composable
fun InteractiveCellUniverse(
    temporalGameOfLifeState: TemporalGameOfLifeState,
    isViewportTracking: Boolean,
    setIsViewportTracking: (Boolean) -> Unit,
    windowSizeClass: WindowSizeClass,
    modifier: Modifier = Modifier,
    mutableCellWindowState: MutableCellWindowState = rememberMutableCellWindowState(),
    trackingCellWindowState: TrackingCellWindowState = rememberTrackingCellWindowState(temporalGameOfLifeState),
) {
    val viewportInteractionConfig = remember(isViewportTracking, mutableCellWindowState, trackingCellWindowState) {
        if (isViewportTracking) {
            ViewportInteractionConfig.Tracking(
                trackingCellWindowState = trackingCellWindowState,
                syncableMutableCellWindowStates = listOf(mutableCellWindowState),
            )
        } else {
            ViewportInteractionConfig.Navigable(
                mutableCellWindowState = mutableCellWindowState,
            )
        }
    }

    Box(modifier = modifier.fillMaxSize()) {
        MutableCellWindow(
            gameOfLifeState = temporalGameOfLifeState,
            modifier = Modifier.testTag("MutableCellWindow"),
            viewportInteractionConfig = viewportInteractionConfig,
        )

        InteractiveCellUniverseOverlay(
            temporalGameOfLifeState = temporalGameOfLifeState,
            cellWindowState = mutableCellWindowState,
            isViewportTracking = isViewportTracking,
            setIsViewportTracking = setIsViewportTracking,
            windowSizeClass = windowSizeClass,
        )
    }
}
