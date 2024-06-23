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

import androidx.compose.animation.core.AnimationSpec
import androidx.compose.animation.core.DecayAnimationSpec
import androidx.compose.foundation.ExperimentalFoundationApi
import androidx.compose.foundation.gestures.AnchoredDraggableState
import androidx.compose.runtime.saveable.Saver

@ExperimentalFoundationApi
actual fun <T> AnchoredDraggableState(
    initialValue: T,
    positionalThreshold: (totalDistance: Float) -> Float,
    velocityThreshold: () -> Float,
    snapAnimationSpec: AnimationSpec<Float>,
    decayAnimationSpec: DecayAnimationSpec<Float>,
): AnchoredDraggableState<T> = AnchoredDraggableState(
    initialValue = initialValue,
    positionalThreshold = positionalThreshold,
    velocityThreshold = velocityThreshold,
    animationSpec = snapAnimationSpec,
)

@ExperimentalFoundationApi
actual fun <T : Any> AnchoredDraggableStateSaver(
    positionalThreshold: (totalDistance: Float) -> Float,
    velocityThreshold: () -> Float,
    snapAnimationSpec: AnimationSpec<Float>,
    decayAnimationSpec: DecayAnimationSpec<Float>,
): Saver<AnchoredDraggableState<T>, T> = AnchoredDraggableState.Saver(
    positionalThreshold = positionalThreshold,
    velocityThreshold = velocityThreshold,
    animationSpec = snapAnimationSpec,
)
