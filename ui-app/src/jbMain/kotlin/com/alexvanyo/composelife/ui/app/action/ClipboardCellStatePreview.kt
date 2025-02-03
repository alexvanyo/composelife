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
import androidx.compose.foundation.layout.Arrangement
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.Row
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.layout.height
import androidx.compose.foundation.layout.padding
import androidx.compose.material.icons.Icons
import androidx.compose.material.icons.filled.ContentPaste
import androidx.compose.material.icons.filled.Error
import androidx.compose.material.icons.filled.PushPin
import androidx.compose.material.icons.filled.Warning
import androidx.compose.material3.Card
import androidx.compose.material3.ExperimentalMaterial3Api
import androidx.compose.material3.Icon
import androidx.compose.material3.IconButton
import androidx.compose.material3.IconToggleButton
import androidx.compose.material3.PlainTooltip
import androidx.compose.material3.Text
import androidx.compose.material3.TooltipBox
import androidx.compose.material3.TooltipDefaults
import androidx.compose.material3.rememberTooltipState
import androidx.compose.runtime.Composable
import androidx.compose.runtime.remember
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.draw.clipToBounds
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.model.DeserializationResult
import com.alexvanyo.composelife.model.GameOfLifeState
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResource
import com.alexvanyo.composelife.ui.app.component.GameOfLifeProgressIndicatorInjectEntryPoint
import com.alexvanyo.composelife.ui.app.component.GameOfLifeProgressIndicatorLocalEntryPoint
import com.alexvanyo.composelife.ui.app.resources.DeserializationFailed
import com.alexvanyo.composelife.ui.app.resources.Paste
import com.alexvanyo.composelife.ui.app.resources.Pin
import com.alexvanyo.composelife.ui.app.resources.Strings
import com.alexvanyo.composelife.ui.app.resources.Unpin
import com.alexvanyo.composelife.ui.app.resources.Warnings
import com.alexvanyo.composelife.ui.cells.CellWindowInjectEntryPoint
import com.alexvanyo.composelife.ui.cells.CellWindowLocalEntryPoint
import com.alexvanyo.composelife.ui.cells.ThumbnailImmutableCellWindow
import com.alexvanyo.composelife.ui.cells.ViewportInteractionConfig
import com.alexvanyo.composelife.ui.cells.cellStateDragAndDropSource
import com.alexvanyo.composelife.ui.cells.rememberTrackingCellWindowViewportState

interface ClipboardCellStatePreviewInjectEntryPoint :
    CellWindowInjectEntryPoint,
    GameOfLifeProgressIndicatorInjectEntryPoint

interface ClipboardCellStatePreviewLocalEntryPoint :
    CellWindowLocalEntryPoint,
    GameOfLifeProgressIndicatorLocalEntryPoint

/**
 * Renders the current clipboard as a cell-state, if possible.
 */
context(ClipboardCellStatePreviewInjectEntryPoint, ClipboardCellStatePreviewLocalEntryPoint)
@Suppress("LongParameterList")
@Composable
fun ClipboardCellStatePreview(
    deserializationResult: DeserializationResult,
    isPinned: Boolean,
    onPaste: () -> Unit,
    onPinChanged: () -> Unit,
    onViewDeserializationInfo: () -> Unit,
    modifier: Modifier = Modifier,
) {
    Card(
        modifier = modifier
            .fillMaxWidth()
            .height(160.dp),
    ) {
        AnimatedContent(
            targetState = deserializationResult,
            modifier = Modifier.fillMaxWidth(),
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
                    is DeserializationResult.Successful -> {
                        LoadedCellStatePreview(
                            deserializationResult = targetState,
                            isPinned = isPinned,
                            onPaste = onPaste,
                            onPinChanged = onPinChanged,
                            onViewDeserializationInfo = onViewDeserializationInfo,
                        )
                    }
                    is DeserializationResult.Unsuccessful -> {
                        Row(
                            modifier = Modifier.padding(8.dp),
                            horizontalArrangement = Arrangement.spacedBy(16.dp),
                            verticalAlignment = Alignment.CenterVertically,
                        ) {
                            Text(parameterizedStringResource(Strings.DeserializationFailed))
                            IconButton(
                                onClick = onViewDeserializationInfo,
                            ) {
                                Icon(
                                    imageVector = Icons.Default.Error,
                                    contentDescription = null,
                                )
                            }
                        }
                    }
                }
            }
        }
    }
}

context(CellWindowInjectEntryPoint, CellWindowLocalEntryPoint)
@Suppress("LongMethod", "LongParameterList")
@OptIn(ExperimentalMaterial3Api::class)
@Composable
fun LoadedCellStatePreview(
    deserializationResult: DeserializationResult.Successful,
    isPinned: Boolean,
    onPaste: () -> Unit,
    onPinChanged: () -> Unit,
    onViewDeserializationInfo: () -> Unit,
    modifier: Modifier = Modifier,
) {
    val gameOfLifeState = remember(deserializationResult) {
        GameOfLifeState(deserializationResult.cellState)
    }

    Row(
        modifier = modifier.fillMaxWidth(),
        verticalAlignment = Alignment.CenterVertically,
    ) {
        ThumbnailImmutableCellWindow(
            gameOfLifeState = gameOfLifeState,
            viewportInteractionConfig = ViewportInteractionConfig.Tracking(
                rememberTrackingCellWindowViewportState(gameOfLifeState),
            ),
            modifier = Modifier
                .weight(1f)
                .clipToBounds()
                .cellStateDragAndDropSource(getCellState = { deserializationResult.cellState }),
            inOverlay = true,
        )
        Column {
            TooltipBox(
                positionProvider = TooltipDefaults.rememberTooltipPositionProvider(),
                tooltip = {
                    PlainTooltip {
                        Text(parameterizedStringResource(Strings.Paste))
                    }
                },
                state = rememberTooltipState(),
            ) {
                IconButton(
                    onClick = onPaste,
                ) {
                    Icon(
                        imageVector = Icons.Default.ContentPaste,
                        contentDescription = parameterizedStringResource(Strings.Paste),
                    )
                }
            }
            TooltipBox(
                positionProvider = TooltipDefaults.rememberTooltipPositionProvider(),
                tooltip = {
                    PlainTooltip {
                        Text(parameterizedStringResource(if (isPinned) Strings.Unpin else Strings.Pin))
                    }
                },
                state = rememberTooltipState(),
            ) {
                IconToggleButton(
                    checked = isPinned,
                    onCheckedChange = { onPinChanged() },
                ) {
                    Icon(
                        imageVector = if (isPinned) Icons.Filled.PushPin else Icons.Default.PushPin,
                        contentDescription = parameterizedStringResource(if (isPinned) Strings.Unpin else Strings.Pin),
                    )
                }
            }
            if (deserializationResult.warnings.isNotEmpty()) {
                TooltipBox(
                    positionProvider = TooltipDefaults.rememberTooltipPositionProvider(),
                    tooltip = {
                        PlainTooltip {
                            Text(parameterizedStringResource(Strings.Warnings))
                        }
                    },
                    state = rememberTooltipState(),
                ) {
                    IconButton(
                        onClick = onViewDeserializationInfo,
                    ) {
                        Icon(
                            imageVector = Icons.Default.Warning,
                            contentDescription = parameterizedStringResource(Strings.Warnings),
                        )
                    }
                }
            }
        }
    }
}
