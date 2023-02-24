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

import android.util.Log
import androidx.compose.animation.core.Animatable
import androidx.compose.animation.core.AnimationSpec
import androidx.compose.animation.core.AnimationVector1D
import androidx.compose.animation.core.VectorConverter
import androidx.compose.animation.core.VisibilityThreshold
import androidx.compose.animation.core.spring
import androidx.compose.foundation.layout.WindowInsets
import androidx.compose.foundation.layout.asPaddingValues
import androidx.compose.foundation.layout.windowInsetsPadding
import androidx.compose.runtime.MutableState
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.runtime.setValue
import androidx.compose.ui.Modifier
import androidx.compose.ui.composed
import androidx.compose.ui.layout.onPlaced
import androidx.compose.ui.unit.Density
import androidx.compose.ui.unit.LayoutDirection
import kotlinx.coroutines.launch

/**
 * An extension of [Modifier.windowInsetsPadding] that allows animating to a [targetWindowInsets].
 *
 * This handles a few edge cases better than trying to animate manually using [WindowInsets.asPaddingValues] due to
 * the intricacies of when insets are available to calculate against.
 *
 * Conceptually, this is sort of like doing the following, except the following isn't quite possible:
 * ```
 * Modifier.windowInsetsPadding(animateWindowInsetsAsState(targetWindowInsets, animationSpec, label))
 * ```
 */
fun Modifier.animatedWindowInsetsPadding(
    targetWindowInsets: WindowInsets,
    animationSpec: AnimationSpec<Int> = spring(visibilityThreshold = Int.VisibilityThreshold),
    label: String = "WindowInsetsPaddingAnimation",
): Modifier = composed {
    val leftAnimatable = remember { mutableStateOf<Animatable<Int, AnimationVector1D>?>(null) }
    val topAnimatable = remember { mutableStateOf<Animatable<Int, AnimationVector1D>?>(null) }
    val rightAnimatable = remember { mutableStateOf<Animatable<Int, AnimationVector1D>?>(null) }
    val bottomAnimatable = remember { mutableStateOf<Animatable<Int, AnimationVector1D>?>(null) }

    /**
     * `true` if we have been placed
     */
    var isPlaced by remember { mutableStateOf(false) }

    val scope = rememberCoroutineScope()

    val animatedInsets = remember(targetWindowInsets, animationSpec) {
        object : WindowInsets {
            private fun MutableState<Animatable<Int, AnimationVector1D>?>.animateTo(target: Int): Int {
                val currentAnimatable = value
                // We may not have correct insets in initial measure calls until we have been placed
                // Therefore, only start tracking potential animations once we have been placed to avoid animating
                // from incorrect inset values
                val animatable = if (currentAnimatable == null || !isPlaced) {
                    Animatable(target, Int.VectorConverter, Int.VisibilityThreshold, label)
                } else {
                    currentAnimatable.apply {
                        if (targetValue != target) {
                            Log.d("vanyo", "animating to $target")
                            scope.launch {
                                animateTo(target, animationSpec)
                            }
                        }
                    }
                }
                value = animatable
                return animatable.value
            }

            override fun getBottom(density: Density): Int =
                bottomAnimatable.animateTo(targetWindowInsets.getBottom(density))

            override fun getLeft(density: Density, layoutDirection: LayoutDirection): Int =
                leftAnimatable.animateTo(targetWindowInsets.getLeft(density, layoutDirection))

            override fun getRight(density: Density, layoutDirection: LayoutDirection): Int =
                rightAnimatable.animateTo(targetWindowInsets.getRight(density, layoutDirection))

            override fun getTop(density: Density): Int =
                topAnimatable.animateTo(targetWindowInsets.getBottom(density))
        }
    }

    this
        .onPlaced { isPlaced = true }
        .windowInsetsPadding(animatedInsets)
}
