/*
 * Copyright 2023 The Android Open Source Project
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

package com.alexvanyo.composelife.ui.wear

import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.runtime.setValue
import androidx.compose.runtime.snapshotFlow
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.graphics.ImageBitmap
import androidx.compose.ui.graphics.asImageBitmap
import androidx.compose.ui.graphics.toArgb
import androidx.wear.watchface.DrawMode
import androidx.wear.watchface.RenderParameters
import androidx.wear.watchface.editor.EditorSession
import androidx.wear.watchface.style.WatchFaceLayer
import com.alexvanyo.composelife.updatable.Updatable
import com.alexvanyo.composelife.wear.watchface.configuration.getGameOfLifeColor
import com.alexvanyo.composelife.wear.watchface.configuration.setGameOfLifeColor
import kotlinx.coroutines.flow.combine
import kotlinx.coroutines.launch
import kotlinx.coroutines.yield

interface WatchFaceConfigState : Updatable {
    val preview: ImageBitmap?

    var color: Color

    fun openComplicationDataSourceChooser(id: Int)
}

@Composable
fun rememberWatchFaceConfigState(
    editorSession: EditorSession
): WatchFaceConfigState {
    val coroutineScope = rememberCoroutineScope()

    var preview: ImageBitmap? by remember { mutableStateOf(null) }

    return remember(editorSession) {
        object : WatchFaceConfigState {
            override val preview: ImageBitmap? get() = preview

            override var color: Color by mutableStateOf(
                with(editorSession.userStyleSchema) {
                    editorSession.userStyle.value.getGameOfLifeColor()
                }
            )

            override fun openComplicationDataSourceChooser(id: Int) {
                coroutineScope.launch {
                    editorSession.openComplicationDataSourceChooser(id)
                }
            }

            override suspend fun update(): Nothing = kotlinx.coroutines.coroutineScope {
                launch {
                    combine(
                        editorSession.userStyle,
                        editorSession.complicationsPreviewData,
                    ) { _, complicationsPreviewData ->
                        yield()
                        preview = editorSession.renderWatchFaceToBitmap(
                            renderParameters = RenderParameters(
                                DrawMode.INTERACTIVE,
                                WatchFaceLayer.ALL_WATCH_FACE_LAYERS,
                                RenderParameters.HighlightLayer(
                                    RenderParameters.HighlightedElement.AllComplicationSlots,
                                    Color.Red.toArgb(),
                                    Color(0, 0, 0, 128).toArgb(),
                                )
                            ),
                            instant = editorSession.previewReferenceInstant,
                            slotIdToComplicationData = complicationsPreviewData,
                        ).asImageBitmap()
                    }
                        .collect {}
                }

                launch {
                    snapshotFlow { color }
                        .collect { newColor ->
                            editorSession.userStyle.value =
                                editorSession.userStyle.value.toMutableUserStyle().apply {
                                    with(editorSession.userStyleSchema) {
                                        setGameOfLifeColor(newColor)
                                    }
                                }.toUserStyle()
                        }
                }
            }.let { error("combine should not complete normally") }
        }
    }
}
