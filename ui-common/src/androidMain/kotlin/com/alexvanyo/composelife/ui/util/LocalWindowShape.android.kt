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

package com.alexvanyo.composelife.ui.util

import android.os.Build
import android.view.RoundedCorner
import androidx.annotation.RequiresApi
import androidx.compose.runtime.Composable
import androidx.compose.runtime.derivedStateOf
import androidx.compose.runtime.getValue
import androidx.compose.runtime.remember
import androidx.compose.ui.geometry.CornerRadius
import androidx.compose.ui.geometry.RoundRect
import androidx.compose.ui.graphics.Path
import androidx.compose.ui.graphics.asComposePath
import androidx.compose.ui.platform.LocalWindowInfo
import androidx.compose.ui.unit.IntSize
import androidx.compose.ui.unit.toIntRect
import androidx.compose.ui.unit.toRect
import androidx.core.view.WindowInsetsCompat

@Composable
actual fun currentWindowShape(): WindowShape {
    val windowInsetsHolder = LocalWindowInsetsHolder.current
    val windowInfo = LocalWindowInfo.current
    return remember(windowInsetsHolder, windowInfo) {
        object : WindowShape {
            override val path by
                derivedStateOf {
                    getDisplayShapePath(windowInsetsHolder.windowInsets, windowInfo.containerSize)
                }
        }
    }
}

private fun getDisplayShapePath(windowInsets: WindowInsetsCompat?, windowSize: IntSize): Path {
    val platformInsets = windowInsets?.toWindowInsets()
    return if (Build.VERSION.SDK_INT >= 34 && platformInsets != null) {
        platformInsets.getPathFromDisplayShape()
    } else {
        null
    } ?: if (Build.VERSION.SDK_INT >= 31 && platformInsets != null) {
        platformInsets.getPathFromRoundedCorners(windowSize)
    } else {
        null
    } ?: getPathFromFrame(windowSize)
}

@Suppress("SwallowedException")
@RequiresApi(34)
private fun android.view.WindowInsets.getPathFromDisplayShape(): Path? =
    try {
        displayShape?.path?.asComposePath()
    } catch (exception: IllegalArgumentException) {
        null
    }

@RequiresApi(31)
private fun android.view.WindowInsets.getPathFromRoundedCorners(windowSize: IntSize): Path =
    Path().apply {
        addRoundRect(
            RoundRect(
                rect = windowSize.toIntRect().toRect(),
                topLeft = getRoundedCorner(
                    RoundedCorner.POSITION_TOP_LEFT,
                )?.toCornerRadius() ?: CornerRadius.Zero,
                topRight = getRoundedCorner(
                    RoundedCorner.POSITION_TOP_RIGHT,
                )?.toCornerRadius() ?: CornerRadius.Zero,
                bottomLeft = getRoundedCorner(
                    RoundedCorner.POSITION_BOTTOM_LEFT,
                )?.toCornerRadius() ?: CornerRadius.Zero,
                bottomRight = getRoundedCorner(
                    RoundedCorner.POSITION_BOTTOM_RIGHT,
                )?.toCornerRadius() ?: CornerRadius.Zero,
            ),
        )
    }

@RequiresApi(31)
private fun getPathFromFrame(windowSize: IntSize): Path =
    Path().apply {
        addRect(
            windowSize.toIntRect().toRect(),
        )
    }

@RequiresApi(31)
private fun RoundedCorner.toCornerRadius(): CornerRadius =
    CornerRadius(x = radius.toFloat())
