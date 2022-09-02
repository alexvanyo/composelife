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

package com.alexvanyo.composelife.ui.cells

import androidx.compose.animation.core.animateFloatAsState
import androidx.compose.runtime.Composable
import androidx.compose.runtime.DisposableEffect
import androidx.compose.runtime.Stable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.setValue
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.geometry.Rect
import androidx.compose.ui.unit.IntRect
import com.alexvanyo.composelife.model.GameOfLifeState
import kotlin.math.max
import kotlin.math.min

/**
 * A viewport state that tracks the overall pattern to enable autofitting and keeping the entire pattern in view.
 */
@Stable
interface TrackingCellWindowState {

    /**
     * Calculates the [CellWindowViewport], with a bit of additional information.
     *
     * The [baseCellWidth] and [baseCellHeight] return the width and height of the available viewport in cell
     * coordinates for the base scale of `1`.
     *
     * The [centerOffset] returns the x and y proportion of whether the center will be placed within the viewport.
     */
    fun calculateCellWindowViewport(
        baseCellWidth: Float,
        baseCellHeight: Float,
        centerOffset: Offset,
    ): CellWindowViewport

    companion object {
        /**
         * The default number of cells to add as padding around the tracking viewport.
         */
        const val defaultCellPadding = 2.0f
    }
}

/**
 * Remembers the [TrackingCellWindowState], based on the [gameOfLifeState].
 *
 * As the [gameOfLifeState] updates, the [TrackingCellWindowState] will update the returned viewport based on the
 * most recent bounding boxes seen.
 */
@Composable
fun rememberTrackingCellWindowState(
    gameOfLifeState: GameOfLifeState,
    cellPadding: Float = TrackingCellWindowState.defaultCellPadding,
): TrackingCellWindowState {
    /**
     * Keep track of the bounding boxes we have had a chance to display.
     */
    var boundingBoxTracker by remember {
        mutableStateOf(listOf(gameOfLifeState.cellState.boundingBox))
    }

    /**
     * Keep around a marker to avoid adding the first cell state to the tracker twice.
     */
    var isFirstCellState by remember { mutableStateOf(true) }

    /**
     * Update the tracker, keeping only the most recent bounding boxes.
     */
    DisposableEffect(gameOfLifeState, gameOfLifeState.cellState) {
        if (isFirstCellState) {
            isFirstCellState = false
        } else {
            boundingBoxTracker = (boundingBoxTracker + listOf(gameOfLifeState.cellState.boundingBox)).takeLast(5)
        }
        onDispose {}
    }

    /**
     * Compute the bounding box that encompasses all of the tracked bounding boxes.
     */
    val maxBoundingBox = boundingBoxTracker.reduce { a, b ->
        IntRect(
            left = min(a.left, b.left),
            right = max(a.right, b.right),
            top = min(a.top, b.top),
            bottom = max(a.bottom, b.bottom),
        )
    }

    val targetBoundingBoxLeft by animateFloatAsState(maxBoundingBox.left - cellPadding)
    val targetBoundingBoxRight by animateFloatAsState(maxBoundingBox.right + cellPadding)
    val targetBoundingBoxTop by animateFloatAsState(maxBoundingBox.top - cellPadding)
    val targetBoundingBoxBottom by animateFloatAsState(maxBoundingBox.bottom + cellPadding)

    /**
     * Create the target bounding box to display in cell coordinates.
     */
    val targetBoundingBox = Rect(
        left = targetBoundingBoxLeft,
        right = targetBoundingBoxRight,
        top = targetBoundingBoxTop,
        bottom = targetBoundingBoxBottom,
    )

    return object : TrackingCellWindowState {
        override fun calculateCellWindowViewport(
            baseCellWidth: Float,
            baseCellHeight: Float,
            centerOffset: Offset,
        ): CellWindowViewport {
            /**
             * Compute the scale as the smallest (more zoomed out) to show the necessary height and width.
             */
            val scale = min(
                baseCellHeight / targetBoundingBox.height,
                baseCellWidth / targetBoundingBox.width,
            )

            /**
             * Compute the offset so that the entire target bounding box will be shown.
             */
            val offset = targetBoundingBox.topLeft + Offset(
                targetBoundingBox.width * centerOffset.x,
                targetBoundingBox.height * centerOffset.y,
            )

            return CellWindowViewport(
                offset = offset,
                scale = scale,
            )
        }
    }
}
