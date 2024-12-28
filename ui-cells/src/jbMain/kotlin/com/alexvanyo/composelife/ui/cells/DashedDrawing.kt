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

import androidx.annotation.FloatRange
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.geometry.Rect
import androidx.compose.ui.geometry.toRect
import androidx.compose.ui.graphics.BlendMode
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.graphics.ColorFilter
import androidx.compose.ui.graphics.StrokeCap
import androidx.compose.ui.graphics.drawscope.DrawScope
import androidx.compose.ui.graphics.drawscope.Stroke

/**
 * Draws a dashed line rectangle, with intervals and phase applied symmetrically.
 *
 * The dashed line effect is drawn in 8 line segments: from the middle of each side,
 * to each corner.
 */
internal fun DrawScope.drawDashedRect(
    selectionColor: Color,
    strokeWidth: Float,
    intervals: FloatArray,
    phase: Float = 0f,
    rect: Rect = size.toRect(),
) {
    // Draw the selection outlines in a way that is symmetric, and hides the extra of the lines near the
    // corners with the selection handles
    listOf(
        rect.topCenter to rect.topLeft,
        rect.topCenter to rect.topRight,
        rect.centerLeft to rect.topLeft,
        rect.centerLeft to rect.bottomLeft,
        rect.bottomCenter to rect.bottomLeft,
        rect.bottomCenter to rect.bottomRight,
        rect.centerRight to rect.topRight,
        rect.centerRight to rect.bottomRight,
    ).forEach { (start, end) ->
        drawDashedLine(
            color = selectionColor,
            start = start,
            end = end,
            strokeWidth = strokeWidth,
            intervals = intervals,
            phase = phase,
        )
    }
}

@Suppress("LongParameterList")
internal expect fun DrawScope.drawDashedLine(
    color: Color,
    start: Offset,
    end: Offset,
    intervals: FloatArray,
    phase: Float = 0f,
    strokeWidth: Float = Stroke.HairlineWidth,
    cap: StrokeCap = Stroke.DefaultCap,
    @FloatRange(from = 0.0, to = 1.0) alpha: Float = 1.0f,
    colorFilter: ColorFilter? = null,
    blendMode: BlendMode = DrawScope.DefaultBlendMode,
)
