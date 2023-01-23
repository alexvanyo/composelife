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
import androidx.compose.foundation.shape.CircleShape
import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.runtime.saveable.listSaver
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.saveable.rememberSaveableStateHolder
import androidx.compose.runtime.setValue
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.draw.clip
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.graphics.ImageBitmap
import androidx.compose.ui.graphics.asImageBitmap
import androidx.compose.ui.platform.LocalConfiguration
import androidx.compose.ui.res.imageResource
import androidx.compose.ui.unit.dp
import androidx.lifecycle.lifecycleScope
import androidx.wear.compose.material.SwipeToDismissBox
import androidx.wear.watchface.DrawMode
import androidx.wear.watchface.RenderParameters
import androidx.wear.watchface.editor.EditorSession
import androidx.wear.watchface.style.WatchFaceLayer
import com.alexvanyo.composelife.navigation.BackstackEntry
import com.alexvanyo.composelife.navigation.MutableBackstackNavigationController
import com.alexvanyo.composelife.navigation.canNavigateBack
import com.alexvanyo.composelife.navigation.currentEntry
import com.alexvanyo.composelife.navigation.popBackstack
import com.alexvanyo.composelife.snapshotstateset.mutableStateSetOf
import com.alexvanyo.composelife.updatable.Updatable
import com.alexvanyo.composelife.wear.theme.ComposeLifeTheme
import kotlinx.coroutines.flow.combine
import kotlinx.coroutines.launch
import kotlinx.coroutines.yield
import java.util.UUID

class WatchFaceConfigActivity : AppCompatActivity() {

    private lateinit var editorSession: EditorSession

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)

        lifecycleScope.launch {
            editorSession = EditorSession.createOnWatchEditorSession(this@WatchFaceConfigActivity)
        }

        setContent {
            val watchFaceConfigState = remember(editorSession) {
                WatchFaceConfigState(editorSession)
            }
            LaunchedEffect(watchFaceConfigState) {
                watchFaceConfigState.update()
            }
            ComposeLifeTheme {
                WatchFaceConfigScreen(watchFaceConfigState)
            }
        }
    }
}

class WatchFaceConfigState(
    private val editorSession: EditorSession,
) : Updatable {

    var preview: Bitmap? by mutableStateOf(null)
        private set

    suspend fun openComplicationDataSourceChooser(id: Int) {
        editorSession.openComplicationDataSourceChooser(id)
    }

    override suspend fun update(): Nothing {
        combine(
            editorSession.userStyle,
            editorSession.complicationsPreviewData,
        ) { _, complicationsPreviewData ->
            yield()
            preview = editorSession.renderWatchFaceToBitmap(
                renderParameters = RenderParameters(
                    DrawMode.INTERACTIVE,
                    WatchFaceLayer.ALL_WATCH_FACE_LAYERS,
                    null
                ),
                instant = editorSession.previewReferenceInstant,
                slotIdToComplicationData = complicationsPreviewData,
            )
        }
            .collect {}

        error("combine should not complete normally")
    }
}

@Composable
fun WatchFaceConfigScreen(
    state: WatchFaceConfigState,
) {
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
                val currentPreview = state.preview
                if (currentPreview != null) {
                    WatchFacePreview(
                        previewBitmap = currentPreview,
                        onComplicationClicked = { id ->
                            coroutineScope.launch {
                                state.openComplicationDataSourceChooser(id)
                            }
                        }
                    )
                }
            }
        }
    }
}

@Composable
fun WatchFacePreview(
    previewBitmap: Bitmap,
    onComplicationClicked: (Int) -> Unit,
    modifier: Modifier = Modifier,
) = WatchFacePreview(
    previewImageBitmap = remember(previewBitmap) {
        previewBitmap.asImageBitmap()
    },
    onComplicationClicked = onComplicationClicked,
    modifier = modifier,
)

@Composable
fun WatchFacePreview(
    previewImageBitmap: ImageBitmap,
    onComplicationClicked: (Int) -> Unit,
    modifier: Modifier = Modifier,
) {
    val aspectRatio = previewImageBitmap.width.toFloat() / previewImageBitmap.height
    Box(
        modifier = modifier.aspectRatio(aspectRatio)
    ) {
        Image(
            bitmap = previewImageBitmap,
            contentDescription = "Preview",
            modifier = Modifier
                .fillMaxWidth()
                .then(
                    if (LocalConfiguration.current.isScreenRound) {
                        Modifier.clip(CircleShape)
                    } else {
                        Modifier
                    }
                )
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

@DevicePreviews
@Composable
fun WatchFacePreviewPreview() {
    WatchFacePreview(
        previewImageBitmap = ImageBitmap.imageResource(R.drawable.watchface_square),
        onComplicationClicked = {},
    )
}

@Composable
fun <T> WearNavigationHost(
    navigationController: MutableBackstackNavigationController<T>,
    modifier: Modifier = Modifier,
    content: @Composable (BackstackEntry<out T>) -> Unit,
) {
    val stateHolder = rememberSaveableStateHolder()
    val allKeys = rememberSaveable(
        saver = listSaver(
            save = { it.map(UUID::toString) },
            restore = {
                mutableStateSetOf<UUID>().apply {
                    addAll(it.map(UUID::fromString))
                }
            },
        ),
    ) { mutableStateSetOf<UUID>() }

    SwipeToDismissBox(
        onDismissed = { navigationController.popBackstack() },
        backgroundKey = navigationController.currentEntry.previous?.id ?: remember { UUID.randomUUID() },
        contentKey = navigationController.currentEntry.id,
        hasBackground = navigationController.canNavigateBack,
        modifier = modifier,
    ) { isBackground ->
        val entry = if (isBackground) {
            checkNotNull(navigationController.currentEntry.previous) {
                "Current entry had no previous, should not be showing background!"
            }
        } else {
            navigationController.currentEntry
        }

        key(entry.id) {
            stateHolder.SaveableStateProvider(key = entry.id) {
                content(entry)
            }
        }
    }

    val keySet: Set<UUID> = navigationController.entryMap.keys.toSet()

    LaunchedEffect(keySet) {
        // Remove the state for a given key if it doesn't correspond to an entry in the backstack map
        (allKeys - keySet).forEach(stateHolder::removeState)
        // Keep track of the ids we've seen, to know which ones we may need to clear out later.
        allKeys.addAll(keySet)
    }
}
