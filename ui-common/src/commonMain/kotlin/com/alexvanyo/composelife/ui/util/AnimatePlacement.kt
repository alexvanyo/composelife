/*
 * Copyright 2022 The Android Open Source Project
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

import androidx.compose.animation.core.Animatable
import androidx.compose.animation.core.AnimationSpec
import androidx.compose.animation.core.AnimationVector2D
import androidx.compose.animation.core.Spring
import androidx.compose.animation.core.VectorConverter
import androidx.compose.animation.core.spring
import androidx.compose.foundation.layout.offset
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.runtime.setValue
import androidx.compose.ui.Modifier
import androidx.compose.ui.composed
import androidx.compose.ui.layout.LayoutCoordinates
import androidx.compose.ui.layout.boundsInParent
import androidx.compose.ui.layout.onPlaced
import androidx.compose.ui.platform.LocalLayoutDirection
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.round
import androidx.compose.ui.unit.toIntRect
import kotlinx.coroutines.launch

/**
 * A [Modifier] that animates placement using the given [animationSpec].
 *
 * The [fixedPoint] calculates the coordinate of the content being animated (in the parent's coordinate system) that
 * the placement should be animating with respect to. This is useful, for instance, if the size of the content being
 * animated is changing too. By default, this calculates the top-start corner of the content being animated.
 *
 * The [parentFixedPoint] calculates the coordinate of the parent (in the parent's coordinate system) that the
 * placement should be animating with respect to. This is useful, for instance, if the size of the parent is changing
 * too. By default, this calculates the top-start corner of the parent.
 *
 * The [keys] are a set of keys used to reset that animation. This is useful to reset the animation, if the fixed
 * point calculation is changing.
 */
fun Modifier.animatePlacement(
    vararg keys: Any,
    animationSpec: AnimationSpec<IntOffset> = spring(stiffness = Spring.StiffnessMedium),
    fixedPoint: LayoutDirectionAwareScope.(layoutCoordinates: LayoutCoordinates) -> IntOffset =
        { layoutCoordinates ->
            layoutCoordinates.boundsInParent().topStart.round()
        },
    parentFixedPoint: LayoutDirectionAwareScope.(parentLayoutCoordinates: LayoutCoordinates) -> IntOffset =
        { parentLayoutCoordinates ->
            parentLayoutCoordinates.size.toIntRect().topStart
        },
): Modifier = composed {
    val scope = rememberCoroutineScope()
    var targetOffset by remember { mutableStateOf(IntOffset.Zero) }
    var animatable by remember(keys = keys) {
        mutableStateOf<Animatable<IntOffset, AnimationVector2D>?>(null)
    }
    val layoutDirection = LocalLayoutDirection.current
    val layoutDirectionAwareScope = remember(layoutDirection) {
        object : LayoutDirectionAwareScope {
            override val layoutDirection = layoutDirection
        }
    }
    this
        .onPlaced { layoutCoordinates ->
            with(layoutDirectionAwareScope) {
                // Calculate the alignment coordinate of this node in the parent coordinates, and calculate the offset
                // from that to the fixed point in the parent
                val currentFixedPoint = fixedPoint(layoutCoordinates)
                val currentParentFixedPoint = parentFixedPoint(
                    requireNotNull(layoutCoordinates.parentLayoutCoordinates),
                )
                targetOffset = currentFixedPoint - currentParentFixedPoint
            }
        }
        .offset {
            // Animate to the new target offset when alignment changes.
            val anim = animatable ?: Animatable(targetOffset, IntOffset.VectorConverter)
                .also { animatable = it }
            if (anim.targetValue != targetOffset) {
                scope.launch {
                    anim.animateTo(targetOffset, animationSpec)
                }
            }
            // Offset the child in the opposite direction to the targetOffset, and slowly catch
            // up to zero offset via an animation to achieve an overall animated movement.
            animatable?.let { it.value - targetOffset } ?: IntOffset.Zero
        }
}
