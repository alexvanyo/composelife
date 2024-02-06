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

package com.alexvanyo.composelife.ui.util

import androidx.annotation.FloatRange
import androidx.compose.foundation.layout.WindowInsets
import androidx.compose.runtime.Stable
import androidx.compose.ui.unit.Density
import androidx.compose.ui.unit.LayoutDirection
import androidx.compose.ui.util.lerp

@Stable
fun lerp(start: WindowInsets, stop: WindowInsets, @FloatRange(from = 0.0, to = 1.0) fraction: Float): WindowInsets =
    object : WindowInsets {
        override fun getBottom(density: Density): Int =
            lerp(start.getBottom(density), stop.getBottom(density), fraction)

        override fun getLeft(density: Density, layoutDirection: LayoutDirection): Int =
            lerp(start.getLeft(density, layoutDirection), stop.getLeft(density, layoutDirection), fraction)

        override fun getRight(density: Density, layoutDirection: LayoutDirection): Int =
            lerp(start.getRight(density, layoutDirection), stop.getRight(density, layoutDirection), fraction)

        override fun getTop(density: Density): Int =
            lerp(start.getTop(density), stop.getTop(density), fraction)
    }
