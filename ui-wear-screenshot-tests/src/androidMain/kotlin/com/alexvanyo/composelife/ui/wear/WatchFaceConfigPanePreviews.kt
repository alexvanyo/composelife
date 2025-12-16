/*
 * Copyright 2025 The Android Open Source Project
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
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.graphics.ImageBitmap
import androidx.compose.ui.res.imageResource
import androidx.wear.compose.ui.tooling.preview.WearPreviewDevices
import com.airbnb.android.showkase.annotation.ShowkaseComposable
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.ui.wear.theme.ComposeLifeTheme
import kotlinx.coroutines.awaitCancellation
import com.alexvanyo.composelife.resources.wear.R as resourcesWearR

@ShowkaseComposable
@WearPreviewDevices
@Composable
internal fun WatchFaceConfigPanePreview() {
    ComposeLifeTheme {
        val preview = ImageBitmap.imageResource(id = resourcesWearR.drawable.watchface_square)

        WatchFaceConfigPane(
            state = object : WatchFaceConfigState {
                override suspend fun update(): Nothing = awaitCancellation()

                override var color: Color
                    get() = Color.White
                    set(_) {}

                override var showComplicationsInAmbient: Boolean
                    get() = true
                    set(_) {}

                override val preview get() = ResourceState.Success(preview)

                override fun openComplicationDataSourceChooser(id: Int) = Unit
            },
        )
    }
}
