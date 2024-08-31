/*
 * Copyright 2024 The Android Open Source Project
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

import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.round
import androidx.compose.ui.unit.toOffset
import com.alexvanyo.composelife.model.CellWindow
import com.alexvanyo.composelife.ui.util.DraggableAnchors2D

internal data class GridDraggableAnchors2d(
    private val scaledCellPixelSize: Float,
    private val cellWindow: CellWindow,
) : DraggableAnchors2D<IntOffset> {
    override fun positionOf(anchor: IntOffset): Offset =
        (anchor.toOffset() - cellWindow.topLeft.toOffset()) * scaledCellPixelSize

    override fun hasPositionFor(anchor: IntOffset): Boolean = true
    override fun closestAnchor(position: Offset): IntOffset =
        (position / scaledCellPixelSize).round() + cellWindow.topLeft

    override val size: Int = Int.MAX_VALUE
}
