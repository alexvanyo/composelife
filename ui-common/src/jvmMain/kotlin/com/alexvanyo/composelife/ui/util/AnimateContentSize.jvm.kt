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

import androidx.compose.animation.core.Animatable
import androidx.compose.animation.core.AnimationEndReason
import androidx.compose.animation.core.AnimationSpec
import androidx.compose.animation.core.AnimationVector2D
import androidx.compose.animation.core.FiniteAnimationSpec
import androidx.compose.animation.core.SnapSpec
import androidx.compose.animation.core.VectorConverter
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.runtime.setValue
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.composed
import androidx.compose.ui.draw.clipToBounds
import androidx.compose.ui.layout.IntrinsicMeasurable
import androidx.compose.ui.layout.IntrinsicMeasureScope
import androidx.compose.ui.layout.LayoutModifier
import androidx.compose.ui.layout.Measurable
import androidx.compose.ui.layout.MeasureResult
import androidx.compose.ui.layout.MeasureScope
import androidx.compose.ui.platform.debugInspectorInfo
import androidx.compose.ui.unit.Constraints
import androidx.compose.ui.unit.IntSize
import kotlinx.coroutines.CoroutineScope
import kotlinx.coroutines.launch

/**
 * TODO: Remove once new implementation is available on both desktop and Android.
 */
actual fun Modifier.animateContentSize(
    animationSpec: FiniteAnimationSpec<IntSize>,
    alignment: Alignment,
    finishedListener: ((initialValue: IntSize, targetValue: IntSize) -> Unit)?,
): Modifier = composed(
    inspectorInfo = debugInspectorInfo {
        name = "animateContentSize"
        properties["animationSpec"] = animationSpec
        properties["finishedListener"] = finishedListener
    },
) {
    // TODO: Listener could be a fun interface after 1.4
    val scope = rememberCoroutineScope()
    val animModifier = remember(scope, alignment) {
        SizeAnimationModifier(animationSpec, scope, alignment)
    }
    animModifier.listener = finishedListener
    this.clipToBounds().then(animModifier)
}

/**
 * This class creates a [LayoutModifier] that measures children, and responds to children's size
 * change by animating to that size. The size reported to parents will be the animated size.
 */
private class SizeAnimationModifier(
    val animationSpec: AnimationSpec<IntSize>,
    val coroutineScope: CoroutineScope,
    val alignment: Alignment,
) : LayoutModifierWithPassThroughIntrinsics() {
    var listener: ((startSize: IntSize, endSize: IntSize) -> Unit)? = null

    data class AnimData(
        val anim: Animatable<IntSize, AnimationVector2D>,
        var startSize: IntSize,
    )

    var animData: AnimData? by mutableStateOf(null)

    override fun MeasureScope.measure(
        measurable: Measurable,
        constraints: Constraints,
    ): MeasureResult {
        val placeable = measurable.measure(constraints)
        val measuredSize = IntSize(placeable.width, placeable.height)
        val targetSize = animateTo(measuredSize)
        return layout(targetSize.width, targetSize.height) {
            placeable.place(
                alignment.align(
                    size = placeable.size,
                    space = targetSize,
                    layoutDirection = layoutDirection,
                ),
            )
        }
    }

    fun animateTo(targetSize: IntSize): IntSize {
        val oldData = animData
        val animSpec = animationSpec

        val newData = if (oldData == null || (animSpec is SnapSpec<*> && animSpec.delay == 0)) {
            AnimData(
                Animatable(
                    targetSize,
                    IntSize.VectorConverter,
                    IntSize(1, 1),
                ),
                targetSize,
            )
        } else {
            oldData
        }

        oldData?.run {
            if (targetSize != anim.targetValue) {
                startSize = anim.value
                coroutineScope.launch {
                    val result = anim.animateTo(targetSize, animSpec)
                    if (result.endReason == AnimationEndReason.Finished) {
                        listener?.invoke(startSize, result.endState.value)
                    }
                }
            }
        }

        animData = newData
        return newData.anim.value
    }
}

internal abstract class LayoutModifierWithPassThroughIntrinsics : LayoutModifier {
    final override fun IntrinsicMeasureScope.minIntrinsicWidth(
        measurable: IntrinsicMeasurable,
        height: Int,
    ) = measurable.minIntrinsicWidth(height)

    final override fun IntrinsicMeasureScope.minIntrinsicHeight(
        measurable: IntrinsicMeasurable,
        width: Int,
    ) = measurable.minIntrinsicHeight(width)

    final override fun IntrinsicMeasureScope.maxIntrinsicWidth(
        measurable: IntrinsicMeasurable,
        height: Int,
    ) = measurable.maxIntrinsicWidth(height)

    final override fun IntrinsicMeasureScope.maxIntrinsicHeight(
        measurable: IntrinsicMeasurable,
        width: Int,
    ) = measurable.maxIntrinsicHeight(width)
}
