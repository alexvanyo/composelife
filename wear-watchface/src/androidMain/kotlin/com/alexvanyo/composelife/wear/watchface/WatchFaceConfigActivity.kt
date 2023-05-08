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

package com.alexvanyo.composelife.wear.watchface

import android.content.ComponentName
import android.os.Bundle
import androidx.activity.compose.setContent
import androidx.appcompat.app.AppCompatActivity
import androidx.compose.foundation.background
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.ui.Modifier
import androidx.lifecycle.lifecycleScope
import androidx.wear.compose.material.MaterialTheme
import androidx.wear.watchface.editor.EditorRequest
import androidx.wear.watchface.editor.EditorSession
import androidx.wear.watchface.editor.WatchFaceEditorContract
import com.alexvanyo.composelife.ui.wear.WatchFaceConfigScreen
import com.alexvanyo.composelife.ui.wear.rememberWatchFaceConfigState
import com.alexvanyo.composelife.ui.wear.theme.ComposeLifeTheme
import kotlinx.coroutines.launch

class WatchFaceConfigActivity : AppCompatActivity() {

    private lateinit var editorSession: EditorSession

    override fun onCreate(savedInstanceState: Bundle?) {
        super.onCreate(savedInstanceState)

        // If we don't have the proper intent provided, set a default one for generating baseline profiles and
        // benchmarks
        if (!intent.hasExtra("COMPONENT_NAME_KEY")) {
            intent = WatchFaceEditorContract().createIntent(
                this,
                EditorRequest(
                    watchFaceComponentName = ComponentName(
                        "com.alexvanyo.composelife.wear",
                        "com.alexvanyo.composelife.wear.watchface.GameOfLifeWatchFaceService",
                    ),
                    editorPackageName = "com.alexvanyo.composelife.wear",
                    initialUserStyle = null,
                ),
            )
        }

        lifecycleScope.launch {
            editorSession = EditorSession.createOnWatchEditorSession(this@WatchFaceConfigActivity)
        }

        setContent {
            val watchFaceConfigState = rememberWatchFaceConfigState(editorSession)
            LaunchedEffect(watchFaceConfigState) {
                watchFaceConfigState.update()
            }
            ComposeLifeTheme {
                WatchFaceConfigScreen(
                    state = watchFaceConfigState,
                    modifier = Modifier.background(MaterialTheme.colors.background),
                )
            }
        }
    }
}
