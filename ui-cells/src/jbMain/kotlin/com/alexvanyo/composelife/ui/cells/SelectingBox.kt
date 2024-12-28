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

import androidx.compose.foundation.Canvas
import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.material3.MaterialTheme
import androidx.compose.runtime.Composable
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.unit.dp

/**
 * The selecting box itself.
 */
@Composable
fun SelectingBox(
    // noinspection ComposeModifierWithoutDefault
    modifier: Modifier,
    selectionColor: Color = MaterialTheme.colorScheme.secondary,
) {
    Canvas(
        modifier = modifier.fillMaxSize(),
    ) {
        drawRect(
            color = selectionColor,
            alpha = 0.2f,
        )
        drawDashedRect(
            selectionColor = selectionColor,
            strokeWidth = 2.dp.toPx(),
            intervals = floatArrayOf(
                24.dp.toPx(),
                24.dp.toPx(),
            ),
            phase = 12.dp.toPx(),
        )
    }
}
