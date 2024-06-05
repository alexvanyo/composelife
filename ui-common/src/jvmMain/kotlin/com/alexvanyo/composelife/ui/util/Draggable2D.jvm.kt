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

package com.alexvanyo.composelife.ui.util

import androidx.compose.foundation.ExperimentalFoundationApi
import androidx.compose.foundation.gestures.Draggable2DState
import androidx.compose.foundation.interaction.MutableInteractionSource
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.unit.Velocity
import androidx.compose.foundation.gestures.draggable2D as androidxDraggable2D

@Suppress("LongParameterList")
@OptIn(ExperimentalFoundationApi::class)
actual fun Modifier.draggable2D(
    state: Draggable2DState,
    enabled: Boolean,
    interactionSource: MutableInteractionSource?,
    startDragImmediately: Boolean,
    onDragStarted: (Offset) -> Unit,
    onDragStopped: (Velocity) -> Unit,
    reverseDirection: Boolean,
) = androidxDraggable2D(
    state = state,
    enabled = enabled,
    interactionSource = interactionSource,
    startDragImmediately = startDragImmediately,
    onDragStarted = { onDragStarted(it) },
    onDragStopped = { onDragStopped(it) },
    reverseDirection = reverseDirection,
)
