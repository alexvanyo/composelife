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

import androidx.compose.runtime.Composable
import androidx.compose.runtime.derivedStateOf
import androidx.compose.runtime.getValue
import androidx.compose.runtime.remember
import androidx.compose.ui.graphics.Path
import androidx.compose.ui.platform.LocalWindowInfo
import androidx.compose.ui.unit.toIntRect
import androidx.compose.ui.unit.toRect

@Composable
actual fun currentWindowShape(): WindowShape {
    val windowInfo = LocalWindowInfo.current
    val path by remember(windowInfo) {
        derivedStateOf {
            Path().apply {
                addRect(windowInfo.containerSize.toIntRect().toRect())
            }
        }
    }
    return remember {
        object : WindowShape {
            override val path get() = path
        }
    }
}
