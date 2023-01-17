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

package com.alexvanyo.composelife.wear

import android.graphics.Bitmap
import android.os.Bundle
import androidx.activity.compose.setContent
import androidx.appcompat.app.AppCompatActivity
import androidx.compose.foundation.Image
import androidx.compose.foundation.border
import androidx.compose.foundation.clickable
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.Row
import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.aspectRatio
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.layout.height
import androidx.compose.foundation.lazy.LazyColumn
import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.runtime.setValue
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.graphics.asImageBitmap
import androidx.compose.ui.unit.dp
import androidx.lifecycle.lifecycleScope
import androidx.wear.watchface.DrawMode
import androidx.wear.watchface.RenderParameters
import androidx.wear.watchface.editor.EditorSession
import androidx.wear.watchface.style.WatchFaceLayer
import kotlinx.coroutines.flow.combine
import kotlinx.coroutines.launch
import kotlinx.coroutines.yield

class WatchFaceConfigActivity : AppCompatActivity() {

    private lateinit var editorSession: EditorSession

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)

        var preview by mutableStateOf<Bitmap?>(null)

        lifecycleScope.launch {
            editorSession = EditorSession.createOnWatchEditorSession(this@WatchFaceConfigActivity)

            combine(
                editorSession.userStyle,
                editorSession.complicationsPreviewData,
            ) { _, complicationsPreviewData ->
                yield()
                editorSession.renderWatchFaceToBitmap(
                    renderParameters = RenderParameters(
                        DrawMode.INTERACTIVE,
                        WatchFaceLayer.ALL_WATCH_FACE_LAYERS,
                        null
                    ),
                    instant = editorSession.previewReferenceInstant,
                    slotIdToComplicationData = complicationsPreviewData,
                )
            }
                .collect {
                    preview = it
                }
        }

        setContent {
            val coroutineScope = rememberCoroutineScope()

            LazyColumn {
                item {
                    Spacer(modifier = Modifier.height(32.dp))
                }
                item {
                    Box(
                        contentAlignment = Alignment.Center,
                        modifier = Modifier.fillMaxWidth(),
                    ) {
                        val currentPreview = preview
                        if (currentPreview != null) {
                            WatchFacePreview(
                                previewBitmap = currentPreview,
                                onComplicationClicked = { id ->
                                    coroutineScope.launch {
                                        editorSession.openComplicationDataSourceChooser(id)
                                    }
                                }
                            )
                        }
                    }
                }
            }
        }
    }
}

@Composable
fun WatchFacePreview(
    previewBitmap: Bitmap,
    onComplicationClicked: (Int) -> Unit,
) {
    val previewImageBitmap = remember(previewBitmap) {
        previewBitmap.asImageBitmap()
    }
    val aspectRatio = previewImageBitmap.width.toFloat() / previewImageBitmap.height
    Box(
        modifier = Modifier
            .fillMaxWidth(0.6f)
            .aspectRatio(aspectRatio)
    ) {
        Image(
            bitmap = previewImageBitmap,
            contentDescription = "Preview",
            modifier = Modifier.fillMaxWidth()
        )

        GameOfLifeComplication.values.forEach { gameOfLifeComplication ->
            Column(
                Modifier.fillMaxSize()
            ) {
                Spacer(
                    modifier = Modifier.weight(gameOfLifeComplication.rawBounds.top)
                )

                Row(
                    Modifier
                        .fillMaxWidth()
                        .weight(gameOfLifeComplication.rawBounds.height)
                ) {
                    Spacer(
                        modifier = Modifier.weight(gameOfLifeComplication.rawBounds.left)
                    )

                    Box(
                        Modifier
                            .fillMaxSize()
                            .border(1.dp, Color.Red)
                            .weight(gameOfLifeComplication.rawBounds.width)
                            .clickable {
                                onComplicationClicked(gameOfLifeComplication.id)
                            }
                    )

                    Spacer(
                        modifier = Modifier.weight(1f - gameOfLifeComplication.rawBounds.right)
                    )
                }

                Spacer(
                    modifier = Modifier.weight(1f - gameOfLifeComplication.rawBounds.bottom)
                )
            }
        }
    }
}
