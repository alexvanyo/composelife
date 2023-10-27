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

package com.alexvanyo.composelife.ui.app.component

import androidx.compose.foundation.layout.Box
import androidx.compose.material3.ExperimentalMaterial3Api
import androidx.compose.material3.PlainTooltip
import androidx.compose.material3.TooltipDefaults
import androidx.compose.material3.rememberTooltipState
import androidx.compose.runtime.Composable
import androidx.compose.ui.Modifier

@Composable
@ExperimentalMaterial3Api
actual fun PlainTooltipBox(
    tooltip: @Composable () -> Unit,
    modifier: Modifier,
    content: @Composable TooltipBoxScope.() -> Unit,
) = Box(modifier = modifier) {
    androidx.compose.material3.TooltipBox(
        positionProvider = TooltipDefaults.rememberPlainTooltipPositionProvider(),
        tooltip = {
            PlainTooltip {
                tooltip()
            }
        },
        state = rememberTooltipState(),
    ) {
        with(
            object : TooltipBoxScope {
                override fun Modifier.tooltipAnchor(): Modifier = this
            },
        ) {
            content()
        }
    }
}

actual interface TooltipBoxScope {
    actual fun Modifier.tooltipAnchor(): Modifier
}
