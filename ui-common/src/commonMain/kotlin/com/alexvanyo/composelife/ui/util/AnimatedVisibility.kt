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

import androidx.compose.animation.core.EaseInOut
import androidx.compose.animation.core.Easing
import androidx.compose.animation.core.FiniteAnimationSpec
import androidx.compose.animation.core.Spring
import androidx.compose.animation.core.spring
import androidx.compose.foundation.layout.ColumnScope
import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.runtime.Composable
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.unit.IntSize

/**
 * A version of AnimatedContent that can animate between [TargetState]s, a target of either one state or
 * between two states.
 */
@Suppress("LongParameterList")
@Composable
fun AnimatedVisibility(
    targetState: TargetState<Boolean>,
    modifier: Modifier = Modifier,
    contentAlignment: Alignment = Alignment.TopStart,
    alphaEasing: Easing = Easing({ 0f }, (0.5f to EaseInOut)),
    contentSizeAnimationSpec: FiniteAnimationSpec<IntSize> = spring(stiffness = Spring.StiffnessMediumLow),
    content: @Composable () -> Unit,
) {
    AnimatedContent(
        targetState = targetState,
        modifier = modifier,
        contentAlignment = contentAlignment,
        alphaEasing = alphaEasing,
        contentSizeAnimationSpec = contentSizeAnimationSpec,
    ) { isVisible ->
        if (isVisible) {
            content()
        }
    }
}

/**
 * A version of AnimatedContent that can animate between [TargetState]s, a target of either one state or
 * between two states.
 */
@Suppress("LongParameterList")
@Composable
fun ColumnScope.AnimatedVisibility(
    targetState: TargetState<Boolean>,
    modifier: Modifier = Modifier,
    contentAlignment: Alignment = Alignment.TopStart,
    alphaEasing: Easing = Easing({ 0f }, (0.5f to EaseInOut)),
    contentSizeAnimationSpec: FiniteAnimationSpec<IntSize> = spring(stiffness = Spring.StiffnessMediumLow),
    content: @Composable () -> Unit,
) {
    AnimatedContent(
        targetState = targetState,
        modifier = modifier,
        contentAlignment = contentAlignment,
        alphaEasing = alphaEasing,
        contentSizeAnimationSpec = contentSizeAnimationSpec,
    ) { isVisible ->
        if (isVisible) {
            content()
        } else {
            Spacer(Modifier.fillMaxWidth())
        }
    }
}
