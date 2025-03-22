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
@file:Suppress("MatchingDeclarationName")

package com.alexvanyo.composelife.ui.util

import android.graphics.Insets
import android.view.DisplayShape
import android.view.RoundedCorner
import android.view.WindowInsets
import androidx.annotation.RequiresApi
import androidx.compose.foundation.Canvas
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.runtime.Composable
import androidx.compose.runtime.CompositionLocalProvider
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.graphics.drawscope.Stroke
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.platform.LocalWindowInfo
import androidx.compose.ui.platform.WindowInfo
import androidx.compose.ui.test.DeviceConfigurationOverride
import androidx.compose.ui.test.WindowInsets
import androidx.compose.ui.test.then
import androidx.compose.ui.tooling.preview.Preview
import androidx.compose.ui.unit.DpSize
import androidx.compose.ui.unit.IntSize
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.roundToIntSize
import androidx.core.view.WindowInsetsCompat
import com.airbnb.android.showkase.annotation.ShowkaseComposable

@RequiresApi(34)
@ShowkaseComposable
@Preview
@Composable
internal fun WindowShapeDisplayShapePreview(modifier: Modifier = Modifier) {
    val density = LocalDensity.current
    DeviceConfigurationOverride(
        DeviceConfigurationOverride.WindowInsets(
            windowInsets = WindowInsetsCompat.toWindowInsetsCompat(
                WindowInsets.Builder()
                    .setDisplayShape(
                        @Suppress("MaxLineLength", "MaximumLineLength")
                        createDisplayShape(
                            displayShapeSpec = "m25,0 h250 a25,25 0 0 1 25,25 v350 a25,25 0 0 1 -25,25 h-250 a25,25 0 0 1 -25,-25 v-350 a25,25 0 0 1 25,-25 z",
                            displayWidth = 300,
                            displayHeight = 400,
                            physicalPixelDisplaySizeRatio = density.density,
                            rotation = 0,
                        ),
                    )
                    .setInsets(WindowInsets.Type.statusBars(), Insets.of(0, 100, 0, 0))
                    .build(),
            ),
        ) then DeviceConfigurationOverride.WindowSize(DpSize(300.dp, 400.dp)),
    ) {
        ProvideLocalWindowInsetsHolder {
            val windowShape = currentWindowShape()
            Canvas(modifier = modifier.fillMaxSize()) {
                drawPath(
                    path = windowShape.path,
                    color = Color.Blue,
                    style = Stroke(
                        width = 8.dp.toPx(),
                    ),
                )
            }
        }
    }
}

@Suppress("LongMethod")
@RequiresApi(34)
@ShowkaseComposable
@Preview
@Composable
internal fun WindowShapeRoundedCornerPreview(modifier: Modifier = Modifier) {
    val density = LocalDensity.current
    DeviceConfigurationOverride(
        DeviceConfigurationOverride.WindowInsets(
            windowInsets = WindowInsetsCompat.toWindowInsetsCompat(
                WindowInsets.Builder()
                    .setRoundedCorner(
                        RoundedCorner.POSITION_TOP_LEFT,
                        RoundedCorner(
                            RoundedCorner.POSITION_TOP_LEFT,
                            with(density) { 25.dp.roundToPx() },
                            with(density) { 25.dp.roundToPx() },
                            with(density) { 25.dp.roundToPx() },
                        ),
                    )
                    .setRoundedCorner(
                        RoundedCorner.POSITION_TOP_RIGHT,
                        RoundedCorner(
                            RoundedCorner.POSITION_TOP_RIGHT,
                            with(density) { 25.dp.roundToPx() },
                            with(density) { 275.dp.roundToPx() },
                            with(density) { 25.dp.roundToPx() },
                        ),
                    )
                    .setRoundedCorner(
                        RoundedCorner.POSITION_BOTTOM_LEFT,
                        RoundedCorner(
                            RoundedCorner.POSITION_BOTTOM_LEFT,
                            with(density) { 25.dp.roundToPx() },
                            with(density) { 25.dp.roundToPx() },
                            with(density) { 375.dp.roundToPx() },
                        ),
                    )
                    .setRoundedCorner(
                        RoundedCorner.POSITION_BOTTOM_RIGHT,
                        RoundedCorner(
                            RoundedCorner.POSITION_BOTTOM_RIGHT,
                            with(density) { 25.dp.roundToPx() },
                            with(density) { 275.dp.roundToPx() },
                            with(density) { 375.dp.roundToPx() },
                        ),
                    )
                    .setInsets(WindowInsets.Type.statusBars(), Insets.of(0, 100, 0, 0))
                    .build(),
            ),
        ) then DeviceConfigurationOverride.WindowSize(DpSize(300.dp, 400.dp)),
    ) {
        ProvideLocalWindowInsetsHolder {
            val windowShape = currentWindowShape()
            Canvas(modifier = modifier.fillMaxSize()) {
                drawPath(
                    path = windowShape.path,
                    color = Color.Blue,
                    style = Stroke(
                        width = 8.dp.toPx(),
                    ),
                )
            }
        }
    }
}

@RequiresApi(34)
@ShowkaseComposable
@Preview
@Composable
internal fun WindowShapeRectanglePreview(modifier: Modifier = Modifier) {
    DeviceConfigurationOverride(
        DeviceConfigurationOverride.WindowInsets(
            windowInsets = WindowInsetsCompat.toWindowInsetsCompat(
                WindowInsets.Builder()
                    .setInsets(WindowInsets.Type.statusBars(), Insets.of(0, 100, 0, 0))
                    .setRoundedCorner(RoundedCorner.POSITION_TOP_LEFT, null)
                    .setRoundedCorner(RoundedCorner.POSITION_TOP_RIGHT, null)
                    .setRoundedCorner(RoundedCorner.POSITION_BOTTOM_LEFT, null)
                    .setRoundedCorner(RoundedCorner.POSITION_BOTTOM_RIGHT, null)
                    .build(),
            ),
        ) then DeviceConfigurationOverride.WindowSize(DpSize(300.dp, 400.dp)),
    ) {
        ProvideLocalWindowInsetsHolder {
            val windowShape = currentWindowShape()
            Canvas(modifier = modifier.fillMaxSize()) {
                drawPath(
                    path = windowShape.path,
                    color = Color.Blue,
                    style = Stroke(
                        width = 8.dp.toPx(),
                    ),
                )
            }
        }
    }
}

/**
 * Creates the [DisplayShape] using reflection, since there is no public constructor.
 */
@RequiresApi(34)
fun createDisplayShape(
    displayShapeSpec: String,
    displayWidth: Int,
    displayHeight: Int,
    physicalPixelDisplaySizeRatio: Float,
    rotation: Int,
): DisplayShape {
    val constructor = DisplayShape::class.java
        .getDeclaredConstructor(
            String::class.java,
            Int::class.java,
            Int::class.java,
            Float::class.java,
            Int::class.java,
        )
        .apply {
            isAccessible = true
        }

    return constructor.newInstance(
        displayShapeSpec,
        displayWidth,
        displayHeight,
        physicalPixelDisplaySizeRatio,
        rotation,
    )
}

fun DeviceConfigurationOverride.Companion.WindowSize(
    size: DpSize,
): DeviceConfigurationOverride = DeviceConfigurationOverride { contentUnderTest ->
    val windowInfo = LocalWindowInfo.current
    val density = LocalDensity.current

    val newWindowInfo = object : WindowInfo by windowInfo {
        override val containerSize: IntSize
            get() = with(density) { size.toSize().roundToIntSize() }
    }

    CompositionLocalProvider(LocalWindowInfo provides newWindowInfo) {
        contentUnderTest()
    }
}
