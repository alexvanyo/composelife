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

import androidx.compose.animation.core.snap
import androidx.compose.animation.core.spring
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.material3.MaterialTheme
import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.runtime.saveable.Saver
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.snapshotFlow
import androidx.compose.ui.Modifier
import androidx.compose.ui.draw.alpha
import androidx.compose.ui.draw.clipToBounds
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.platform.testTag
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.util.packInts
import androidx.compose.ui.util.unpackInt1
import androidx.compose.ui.util.unpackInt2
import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.model.CellWindow
import com.alexvanyo.composelife.model.GameOfLifeState
import com.alexvanyo.composelife.sessionvalue.SessionValue
import com.alexvanyo.composelife.ui.util.AnchoredDraggable2DState
import com.alexvanyo.composelife.ui.util.anchoredDraggable2D
import kotlinx.coroutines.flow.collect
import kotlinx.coroutines.flow.onEach

context(CellWindowInjectEntryPoint, CellWindowLocalEntryPoint)
@Suppress("LongParameterList", "LongMethod")
@Composable
internal fun SelectionBoxOverlay(
    selectionSessionState: SessionValue<SelectionState.Selection>,
    setSelectionState: (SelectionState) -> Unit,
    getSelectionCellState: () -> CellState,
    scaledCellPixelSize: Float,
    cellWindow: CellWindow,
    modifier: Modifier = Modifier,
) {
    val handleAnchors = remember(scaledCellPixelSize, cellWindow) {
        GridDraggableAnchors2d(scaledCellPixelSize, cellWindow)
    }

    val initialOffset = selectionSessionState.value.offset

    val currentSelectionSessionState by rememberUpdatedState(selectionSessionState)
    val currentSetSelectionState by rememberUpdatedState(setSelectionState)

    val confirmValueChange = { intOffset: IntOffset ->
        setSelectionState(
            currentSelectionSessionState.value.copy(
                offset = intOffset,
            ),
        )
        true
    }

    val draggable2DState = rememberSaveable(
        saver = Saver(
            save = { packInts(it.currentValue.x, it.currentValue.y) },
            restore = {
                AnchoredDraggable2DState(
                    initialValue = IntOffset(unpackInt1(it), unpackInt2(it)),
                    animationSpec = spring(),
                    confirmValueChange = confirmValueChange,
                )
            },
        ),
    ) {
        AnchoredDraggable2DState(
            initialValue = initialOffset,
            animationSpec = spring(),
            confirmValueChange = confirmValueChange,
        )
    }.apply {
        updateAnchors(
            newAnchors = handleAnchors,
            // Ensure the target value remains the same due to updating the anchors.
            // This keeps the selection box stationary relative to the overall universe.
            newTarget = targetValue,
        )
    }

    // As a side-effect of dragging, update the underlying selection state to match the intermediate selection.
    LaunchedEffect(draggable2DState) {
        snapshotFlow { draggable2DState.currentValue }
            .onEach { intOffset ->
                currentSetSelectionState(
                    currentSelectionSessionState.value.copy(
                        offset = intOffset,
                    ),
                )
            }
            .collect()
    }

    val boundingBox = selectionSessionState.value.cellState.boundingBox

    Box(
        modifier = modifier
            .fillMaxSize()
            .boxLayoutByHandles(
                handleAOffsetCalculator = {
                    draggable2DState.requireOffset()
                },
                handleBOffsetCalculator = {
                    draggable2DState.requireOffset() + Offset(
                        boundingBox.width.toFloat(),
                        0f,
                    ) * scaledCellPixelSize
                },
                handleCOffsetCalculator = {
                    draggable2DState.requireOffset() + Offset(
                        boundingBox.width.toFloat(),
                        boundingBox.height.toFloat(),
                    ) * scaledCellPixelSize
                },
                handleDOffsetCalculator = {
                    draggable2DState.requireOffset() + Offset(
                        0f,
                        boundingBox.height.toFloat(),
                    ) * scaledCellPixelSize
                },
            )
            .cellStateDragAndDropSource(getSelectionCellState)
            .anchoredDraggable2D(draggable2DState)
            .testTag("SelectionBox"),
    ) {
        val gameOfLifeState = remember(selectionSessionState.valueId) {
            GameOfLifeState(selectionSessionState.value.cellState)
        }
        ThumbnailImmutableCellWindow(
            gameOfLifeState = gameOfLifeState,
            viewportInteractionConfig = ViewportInteractionConfig.Tracking(
                trackingCellWindowViewportState = rememberTrackingCellWindowViewportState(
                    gameOfLifeState = gameOfLifeState,
                    trackingWindowSize = 1,
                    cellPadding = 0f,
                ),
                trackingAnimationSpec = snap(),
            ),
            modifier = Modifier
                .matchParentSize()
                .clipToBounds()
                .alpha(0.2f),
        )
        SelectingBox(
            modifier = Modifier.matchParentSize(),
            selectionColor = MaterialTheme.colorScheme.tertiary,
        )
    }
}
