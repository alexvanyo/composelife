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

import androidx.compose.ui.geometry.Rect
import androidx.compose.ui.layout.LayoutCoordinates
import androidx.compose.ui.layout.boundsInParent
import androidx.compose.ui.layout.positionInParent
import androidx.compose.ui.unit.toSize

/**
 * Returns the [Rect] corresponding to the "real" bounds in the parent.
 *
 * This will return the actual bounds in parent when the resulting bounds are empty, unlike
 * [LayoutCoordinates.boundsInParent].
 */
fun LayoutCoordinates.realBoundsInParent(): Rect =
    Rect(
        positionInParent(),
        size.toSize(),
    )
