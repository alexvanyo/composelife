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

import android.content.ClipData
import android.content.ClipDescription
import android.os.Build
import android.view.View
import androidx.compose.foundation.ExperimentalFoundationApi
import androidx.compose.foundation.draganddrop.dragAndDropSource
import androidx.compose.foundation.draganddrop.dragAndDropTarget
import androidx.compose.foundation.gestures.detectTapGestures
import androidx.compose.runtime.Composable
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.ui.Modifier
import androidx.compose.ui.draganddrop.DragAndDropEvent
import androidx.compose.ui.draganddrop.DragAndDropTarget
import androidx.compose.ui.draganddrop.DragAndDropTransferData
import androidx.compose.ui.draganddrop.mimeTypes
import androidx.compose.ui.draganddrop.toAndroidDragEvent
import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.model.DeserializationResult
import com.alexvanyo.composelife.model.RunLengthEncodedCellStateSerializer
import com.alexvanyo.composelife.model.di.CellStateParserProvider
import kotlinx.coroutines.launch

@OptIn(ExperimentalFoundationApi::class)
actual fun Modifier.cellStateDragAndDropSource(
    getCellState: () -> CellState,
): Modifier =
    dragAndDropSource {
        detectTapGestures(
            onLongPress = {
                startTransfer(
                    DragAndDropTransferData(
                        clipData = ClipData.newPlainText(
                            "cellState",
                            RunLengthEncodedCellStateSerializer.serializeToString(getCellState())
                                .joinToString("\n"),
                        ),
                        flags =
                        if (Build.VERSION.SDK_INT >= 24) {
                            View.DRAG_FLAG_GLOBAL
                        } else {
                            0
                        },
                    ),
                )
            },
        )
    }

context(CellStateParserProvider)
@OptIn(ExperimentalFoundationApi::class)
@Composable
@Suppress("ComposeComposableModifier")
actual fun Modifier.cellStateDragAndDropTarget(
    setSelectionToCellState: (CellState) -> Unit,
): Modifier {
    val coroutineScope = rememberCoroutineScope()
    val target = remember(cellStateParser, coroutineScope) {
        object : DragAndDropTarget {
            override fun onDrop(event: DragAndDropEvent): Boolean {
                val clipData = event.toAndroidDragEvent().clipData
                coroutineScope.launch {
                    when (
                        val deserializationResult = cellStateParser.parseCellState(clipData)
                    ) {
                        is DeserializationResult.Successful -> {
                            setSelectionToCellState(deserializationResult.cellState)
                        }
                        is DeserializationResult.Unsuccessful -> {
                            // TODO: Show error for unsuccessful drag and drop
                        }
                    }
                }
                return true
            }
        }
    }

    return dragAndDropTarget(
        shouldStartDragAndDrop = { event ->
            event.mimeTypes().contains(ClipDescription.MIMETYPE_TEXT_PLAIN)
        },
        target = target,
    )
}
