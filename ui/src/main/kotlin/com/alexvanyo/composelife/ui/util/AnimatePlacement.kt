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
import androidx.compose.ui.Alignment
import androidx.compose.ui.ExperimentalComposeUiApi
import androidx.compose.ui.Modifier
import androidx.compose.ui.composed
import androidx.compose.ui.layout.onPlaced
import androidx.compose.ui.layout.positionInParent
import androidx.compose.ui.platform.LocalLayoutDirection
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.round
import kotlinx.coroutines.launch

/**
 * A [Modifier] that animates placement using the given [animationSpec].
 */
@OptIn(ExperimentalComposeUiApi::class)
fun Modifier.animatePlacement(
    animationSpec: AnimationSpec<IntOffset> = spring(stiffness = Spring.StiffnessMedium),
    alignment: Alignment = Alignment.Center
): Modifier = composed {
    val scope = rememberCoroutineScope()
    var targetOffset by remember { mutableStateOf(IntOffset.Zero) }
    var animatable by remember {
        mutableStateOf<Animatable<IntOffset, AnimationVector2D>?>(null)
    }
    val layoutDirection = LocalLayoutDirection.current
    this.onPlaced {
        // Calculate the alignment's position in the parent layout
        targetOffset = it.positionInParent().round() + alignment.align(it.size, it.size * 2, layoutDirection)
    }.offset {
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
