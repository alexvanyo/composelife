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

import android.os.Build
import androidx.annotation.FloatRange
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.graphics.BlendMode
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.graphics.ColorFilter
import androidx.compose.ui.graphics.PathEffect
import androidx.compose.ui.graphics.StrokeCap
import androidx.compose.ui.graphics.drawscope.DrawScope
import kotlin.math.min

/**
 * A compat implementation of [DrawScope.drawLine] with a dashed [PathEffect].
 *
 * [PathEffect.dashPathEffect] doesn't work in hardware acceleration on API 27 and below:
 * [https://issuetracker.google.com/issues/236553602](https://issuetracker.google.com/issues/236553602)
 */
@Suppress("LongParameterList")
internal actual fun DrawScope.drawDashedLine(
    color: Color,
    start: Offset,
    end: Offset,
    intervals: FloatArray,
    phase: Float,
    strokeWidth: Float,
    cap: StrokeCap,
    @FloatRange(from = 0.0, to = 1.0) alpha: Float,
    colorFilter: ColorFilter?,
    blendMode: BlendMode,
) = if (Build.VERSION.SDK_INT >= 28) {
    drawLine(
        color = color,
        start = start,
        end = end,
        strokeWidth = strokeWidth,
        cap = cap,
        pathEffect = PathEffect.dashPathEffect(
            intervals = intervals,
            phase = phase,
        ),
        alpha = alpha,
        colorFilter = colorFilter,
        blendMode = blendMode,
    )
} else {
    var remainingPhase = phase
    var coveredLength = 0f
    val lengthToDraw = (end - start).getDistance()
    val unitDirection = (end - start) / lengthToDraw
    var intervalIndex = 0
    while (true) {
        val intervalLength = intervals[intervalIndex]
        val phaseToRemove = min(remainingPhase, intervalLength)
        remainingPhase -= phaseToRemove
        val intervalLengthToDraw = min(intervalLength - phaseToRemove, lengthToDraw - coveredLength)
        if (intervalLengthToDraw > 0f && intervalIndex % 2 == 0) {
            drawLine(
                color = color,
                start = start + unitDirection * coveredLength,
                end = start + unitDirection * (coveredLength + intervalLengthToDraw),
                strokeWidth = strokeWidth,
                cap = cap,
                alpha = alpha,
                colorFilter = colorFilter,
                blendMode = blendMode,
            )
        }
        if (intervalLength - phaseToRemove >= lengthToDraw - coveredLength) break
        coveredLength += intervalLengthToDraw
        intervalIndex++
        intervalIndex %= intervals.size
    }
}
