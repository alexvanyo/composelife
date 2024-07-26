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

package com.alexvanyo.composelife.geometry

import androidx.annotation.FloatRange
import androidx.compose.runtime.Stable
import androidx.compose.ui.unit.IntSize
import androidx.compose.ui.util.lerp

@Stable
fun lerp(start: IntSize, stop: IntSize, @FloatRange(from = 0.0, to = 1.0) fraction: Float): IntSize =
    IntSize(
        lerp(start.width, stop.width, fraction),
        lerp(start.height, stop.height, fraction),
    )
