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

import androidx.compose.foundation.Canvas
import androidx.compose.foundation.layout.requiredSize
import androidx.compose.runtime.Composable
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.CornerRadius
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.geometry.Size
import androidx.compose.ui.graphics.graphicsLayer
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.unit.Dp
import androidx.compose.ui.unit.IntRect
import androidx.compose.ui.unit.toOffset
import com.alexvanyo.composelife.model.GameOfLifeState
import com.alexvanyo.composelife.preferences.CurrentShape
import com.alexvanyo.composelife.ui.app.theme.ComposeLifeTheme

@Suppress("LongParameterList")
@Composable
fun CanvasNonInteractableCells(
    gameOfLifeState: GameOfLifeState,
    scaledCellDpSize: Dp,
    cellWindow: IntRect,
    shape: CurrentShape,
    pixelOffsetFromCenter: Offset,
    modifier: Modifier = Modifier,
) {
    val scaledCellPixelSize = with(LocalDensity.current) { scaledCellDpSize.toPx() }

    val aliveColor = ComposeLifeTheme.aliveCellColor
    val deadColor = ComposeLifeTheme.deadCellColor

    Canvas(
        modifier = modifier
            .graphicsLayer {
                this.translationX = -pixelOffsetFromCenter.x
                this.translationY = -pixelOffsetFromCenter.y
            }
            .requiredSize(
                scaledCellDpSize * (cellWindow.width + 1),
                scaledCellDpSize * (cellWindow.height + 1),
            ),
    ) {
        drawRect(
            color = deadColor,
        )

        gameOfLifeState.cellState.getAliveCellsInWindow(cellWindow).forEach { cell ->
            when (shape) {
                is CurrentShape.RoundRectangle -> {
                    drawRoundRect(
                        color = aliveColor,
                        topLeft = (cell - cellWindow.topLeft).toOffset() * scaledCellPixelSize +
                            Offset(
                                scaledCellPixelSize * (1f - shape.sizeFraction) / 2f,
                                scaledCellPixelSize * (1f - shape.sizeFraction) / 2f,
                            ),
                        size = Size(scaledCellPixelSize, scaledCellPixelSize) * shape.sizeFraction,
                        cornerRadius = CornerRadius(
                            scaledCellPixelSize * shape.sizeFraction * shape.cornerFraction,
                        ),
                    )
                }
                is CurrentShape.Superellipse -> {
                    // TODO
                    drawRect(
                        color = aliveColor,
                        topLeft = (cell - cellWindow.topLeft).toOffset() * scaledCellPixelSize,
                        size = Size(scaledCellPixelSize, scaledCellPixelSize),
                    )
                }
            }
        }
    }
}
