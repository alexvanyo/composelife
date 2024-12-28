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

import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.foundation.layout.offset
import androidx.compose.runtime.Composable
import androidx.compose.runtime.key
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.graphicsLayer
import androidx.compose.ui.unit.round
import androidx.compose.ui.unit.toOffset
import com.alexvanyo.composelife.model.CellWindow

@Composable
internal fun TransientSelectingBoxOverlay(
    selectionState: SelectionState.SelectingBox.TransientSelectingBox,
    scaledCellPixelSize: Float,
    cellWindow: CellWindow,
    modifier: Modifier = Modifier,
) {
    Box(modifier) {
        val selectionRect = selectionState.rect.translate(-cellWindow.topLeft.toOffset())

        val handleAOffsetCalculator = { selectionRect.topLeft * scaledCellPixelSize }
        val handleBOffsetCalculator = { selectionRect.topRight * scaledCellPixelSize }
        val handleCOffsetCalculator = { selectionRect.bottomRight * scaledCellPixelSize }
        val handleDOffsetCalculator = { selectionRect.bottomLeft * scaledCellPixelSize }

        val handleOffsetCalculators = listOf(
            handleAOffsetCalculator,
            handleBOffsetCalculator,
            handleCOffsetCalculator,
            handleDOffsetCalculator,
        )

        SelectingBox(
            modifier = Modifier
                .fillMaxSize()
                .boxLayoutByHandles(
                    handleAOffsetCalculator = {
                        selectionRect.topLeft * scaledCellPixelSize
                    },
                    handleBOffsetCalculator = {
                        selectionRect.topRight * scaledCellPixelSize
                    },
                    handleCOffsetCalculator = {
                        selectionRect.bottomRight * scaledCellPixelSize
                    },
                    handleDOffsetCalculator = {
                        selectionRect.bottomLeft * scaledCellPixelSize
                    },
                ),
        )

        handleOffsetCalculators.mapIndexed { index, offsetCalculator ->
            key(index) {
                SelectionHandle(
                    isActive = index == 2,
                    modifier = Modifier
                        .offset {
                            offsetCalculator().round()
                        }
                        .graphicsLayer {
                            translationX = -size.width / 2f
                            translationY = -size.height / 2f
                        },
                )
            }
        }
    }
}
