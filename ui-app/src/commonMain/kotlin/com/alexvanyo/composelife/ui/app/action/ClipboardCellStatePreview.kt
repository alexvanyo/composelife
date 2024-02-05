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

package com.alexvanyo.composelife.ui.app.action

import androidx.compose.animation.AnimatedContent
import androidx.compose.animation.core.tween
import androidx.compose.animation.fadeIn
import androidx.compose.animation.fadeOut
import androidx.compose.animation.togetherWith
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.Row
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.layout.height
import androidx.compose.foundation.layout.padding
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.filled.ContentPaste
import androidx.compose.material.icons.filled.PushPin
import androidx.compose.material3.Card
import androidx.compose.material3.ExperimentalMaterial3Api
import androidx.compose.material3.Icon
import androidx.compose.material3.IconButton
import androidx.compose.material3.Text
import androidx.compose.runtime.Composable
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.model.DeserializationResult
import com.alexvanyo.composelife.model.GameOfLifeState
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResource
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.ui.app.cells.CellWindowInteractionState
import com.alexvanyo.composelife.ui.app.cells.CellWindowLocalEntryPoint
import com.alexvanyo.composelife.ui.app.cells.ImmutableCellWindow
import com.alexvanyo.composelife.ui.app.cells.SelectionState
import com.alexvanyo.composelife.ui.app.cells.ViewportInteractionConfig
import com.alexvanyo.composelife.ui.app.cells.rememberTrackingCellWindowViewportState
import com.alexvanyo.composelife.ui.app.component.GameOfLifeProgressIndicator
import com.alexvanyo.composelife.ui.app.component.GameOfLifeProgressIndicatorInjectEntryPoint
import com.alexvanyo.composelife.ui.app.component.GameOfLifeProgressIndicatorLocalEntryPoint
import com.alexvanyo.composelife.ui.app.component.PlainTooltipBox
import com.alexvanyo.composelife.ui.app.resources.Paste
import com.alexvanyo.composelife.ui.app.resources.Pin
import com.alexvanyo.composelife.ui.app.resources.Strings

interface ClipboardCellStatePreviewInjectEntryPoint :
    GameOfLifeProgressIndicatorInjectEntryPoint

interface ClipboardCellStatePreviewLocalEntryPoint :
    CellWindowLocalEntryPoint,
    GameOfLifeProgressIndicatorLocalEntryPoint

/**
 * Renders the current clipboard as a cell-state, if possible.
 */
context(ClipboardCellStatePreviewInjectEntryPoint, ClipboardCellStatePreviewLocalEntryPoint)
@Composable
fun ClipboardCellStatePreview(
    clipboardCellStateResourceState: ResourceState<DeserializationResult>,
    onPaste: () -> Unit,
    onPin: () -> Unit,
    modifier: Modifier = Modifier,
) {
    Card(
        modifier = modifier
            .padding(horizontal = 24.dp)
            .fillMaxWidth()
            .height(160.dp),
    ) {
        AnimatedContent(
            targetState = clipboardCellStateResourceState,
            modifier = modifier.fillMaxWidth(),
            transitionSpec = {
                fadeIn(animationSpec = tween(220, delayMillis = 90))
                    .togetherWith(fadeOut(animationSpec = tween(90)))
            },
            contentAlignment = Alignment.Center,
        ) { targetState ->
            Box(
                modifier = Modifier.fillMaxSize(),
                contentAlignment = Alignment.Center,
            ) {
                when (targetState) {
                    is ResourceState.Failure -> {
                        // TODO
                    }

                    ResourceState.Loading -> {
                        GameOfLifeProgressIndicator()
                    }

                    is ResourceState.Success -> {
                        when (val deserializationResult = targetState.value) {
                            is DeserializationResult.Successful -> {
                                LoadedCellStatePreview(
                                    cellState = deserializationResult.cellState,
                                    onPaste = onPaste,
                                    onPin = onPin,
                                )
                            }
                            is DeserializationResult.Unsuccessful -> {
                                // TODO
                            }
                        }
                    }
                }
            }
        }
    }
}

context(CellWindowLocalEntryPoint)
@OptIn(ExperimentalMaterial3Api::class)
@Composable
fun LoadedCellStatePreview(
    cellState: CellState,
    onPaste: () -> Unit,
    onPin: () -> Unit,
    modifier: Modifier = Modifier,
) {
    val gameOfLifeState = GameOfLifeState(cellState)

    Row(
        modifier = modifier.fillMaxWidth(),
        verticalAlignment = Alignment.CenterVertically,
    ) {
        ImmutableCellWindow(
            gameOfLifeState = gameOfLifeState,
            cellWindowInteractionState = CellWindowInteractionState(
                viewportInteractionConfig = ViewportInteractionConfig.Tracking(
                    rememberTrackingCellWindowViewportState(gameOfLifeState),
                ),
                selectionState = SelectionState.NoSelection,
            ),
            modifier = Modifier.weight(1f),
            inOverlay = true,
        )
        Column {
            PlainTooltipBox(
                tooltip = {
                    Text(parameterizedStringResource(Strings.Paste))
                },
            ) {
                IconButton(
                    onClick = onPaste,
                    modifier = Modifier.tooltipAnchor(),
                ) {
                    Icon(
                        imageVector = Icons.Filled.ContentPaste,
                        contentDescription = parameterizedStringResource(Strings.Paste),
                    )
                }
            }
            PlainTooltipBox(
                tooltip = {
                    Text(parameterizedStringResource(Strings.Pin))
                },
            ) {
                IconButton(
                    onClick = onPin,
                    modifier = Modifier.tooltipAnchor(),
                ) {
                    Icon(
                        imageVector = Icons.Default.PushPin,
                        contentDescription = parameterizedStringResource(Strings.Pin),
                    )
                }
            }
        }
    }
}
