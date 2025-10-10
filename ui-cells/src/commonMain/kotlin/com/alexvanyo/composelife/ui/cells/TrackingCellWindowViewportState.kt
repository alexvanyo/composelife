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

import androidx.annotation.FloatRange
import androidx.annotation.IntRange
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
import com.alexvanyo.composelife.model.CellWindow
import com.alexvanyo.composelife.model.GameOfLifeState
import kotlin.math.max
import kotlin.math.min

/**
 * A viewport state that tracks the overall pattern to enable autofitting and keeping the entire pattern in view.
 */
@Stable
interface TrackingCellWindowViewportState {

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
         * The default number of cell states to use as a window to calculate the maximum bounding box.
         */
        const val defaultTrackingWindowSize = 5

        /**
         * The default number of cells to add as padding around the tracking viewport.
         */
        const val defaultCellPadding = 2.0f
    }
}

/**
 * Remembers the [TrackingCellWindowViewportState], based on the [gameOfLifeState].
 *
 * As the [gameOfLifeState] updates, the [TrackingCellWindowViewportState] will update the returned viewport based on
 * the most recent bounding boxes seen.
 *
 * @param gameOfLifeState the [GameOfLifeState] to track a viewport for as it changes.
 * @param trackingWindowSize the number of consecutive cell states to debounce the tracking by. This avoids bad behavior
 * for quickly repeating patterns that change the bounding box slightly, resulting in jittering. The default value is
 * [TrackingCellWindowViewportState.defaultTrackingWindowSize]
 * @param cellPadding the fractional number of cells to pad the tracking by. The default value is
 * [TrackingCellWindowViewportState.defaultCellPadding].
 */
@Composable
fun rememberTrackingCellWindowViewportState(
    gameOfLifeState: GameOfLifeState,
    @IntRange(from = 1L)
    trackingWindowSize: Int = TrackingCellWindowViewportState.defaultTrackingWindowSize,
    @FloatRange(from = 0.0)
    cellPadding: Float = TrackingCellWindowViewportState.defaultCellPadding,
): TrackingCellWindowViewportState {
    /**
     * Keep track of the bounding boxes we have had a chance to display.
     */
    var previousBoundingBoxes by remember {
        mutableStateOf(emptyList<CellWindow>())
    }

    /**
     * Keep track of whether the current bounding box is included in [previousBoundingBoxes].
     *
     * If it is, then we shouldn't include it again in `currentBoundingBoxes`
     */
    var isCurrentBoundingBoxIncludedInPrevious by remember(gameOfLifeState, gameOfLifeState.cellState) {
        mutableStateOf(false)
    }

    val currentBoundingBoxes = if (isCurrentBoundingBoxIncludedInPrevious) {
        previousBoundingBoxes
    } else {
        previousBoundingBoxes + gameOfLifeState.cellState.boundingBox
    }
        .takeLast(trackingWindowSize)

    DisposableEffect(gameOfLifeState, gameOfLifeState.cellState, trackingWindowSize) {
        previousBoundingBoxes = currentBoundingBoxes
        isCurrentBoundingBoxIncludedInPrevious = true
        onDispose {}
    }

    /**
     * Compute the bounding box that encompasses all of the tracked bounding boxes.
     */
    val maxBoundingBox = currentBoundingBoxes.reduce { a, b ->
        CellWindow(
            IntRect(
                left = min(a.left, b.left),
                right = max(a.right, b.right),
                top = min(a.top, b.top),
                bottom = max(a.bottom, b.bottom),
            ),
        )
    }

    /**
     * Create the target bounding box to display in cell coordinates.
     */
    val boundingBox = Rect(
        left = maxBoundingBox.left - cellPadding,
        right = maxBoundingBox.right + cellPadding,
        top = maxBoundingBox.top - cellPadding,
        bottom = maxBoundingBox.bottom + cellPadding,
    )

    return object : TrackingCellWindowViewportState {
        override fun calculateCellWindowViewport(
            baseCellWidth: Float,
            baseCellHeight: Float,
            centerOffset: Offset,
        ): CellWindowViewport {
            /**
             * Compute the scale as the smallest (more zoomed out) to show the necessary height and width.
             */
            val scale = min(
                baseCellHeight / boundingBox.height,
                baseCellWidth / boundingBox.width,
            )

            /**
             * Compute the offset so that the entire target bounding box will be shown.
             */
            val offset = boundingBox.topLeft + Offset(
                (boundingBox.width - 1) * centerOffset.x,
                (boundingBox.height - 1) * centerOffset.y,
            )

            return CellWindowViewport(
                offset = offset,
                scale = scale,
            )
        }
    }
}
