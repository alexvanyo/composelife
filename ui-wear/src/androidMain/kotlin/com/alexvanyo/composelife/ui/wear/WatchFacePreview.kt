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

import androidx.compose.foundation.Image
import androidx.compose.foundation.clickable
import androidx.compose.foundation.layout.Box
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.Row
import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.aspectRatio
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.shape.CircleShape
import androidx.compose.runtime.Composable
import androidx.compose.ui.Modifier
import androidx.compose.ui.draw.clip
import androidx.compose.ui.graphics.ImageBitmap
import androidx.compose.ui.platform.LocalConfiguration
import androidx.compose.ui.res.imageResource
import com.alexvanyo.composelife.ui.util.WearDevicePreviews
import com.alexvanyo.composelife.wear.watchface.configuration.GameOfLifeComplication
import com.alexvanyo.composelife.wear.watchface.configuration.values
import com.alexvanyo.composelife.resources.wear.R as resourcesWearR

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

@WearDevicePreviews
@Composable
fun WatchFacePreviewPreview() {
    WatchFacePreview(
        previewImageBitmap = ImageBitmap.imageResource(resourcesWearR.drawable.watchface_square),
        onComplicationClicked = {},
    )
}
