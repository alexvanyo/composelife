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

import androidx.compose.animation.AnimatedVisibilityScope
import androidx.compose.foundation.layout.Box
import androidx.compose.runtime.Composable
import androidx.compose.runtime.ProvidableCompositionLocal
import androidx.compose.runtime.compositionLocalOf
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.Path
import androidx.compose.ui.layout.LookaheadScope
import com.alexvanyo.composelife.ui.util.SharedTransitionScope.SharedContentState

@Composable
fun SharedTransitionLayout(
    modifier: Modifier = Modifier,
    content: @Composable SharedTransitionScope.() -> Unit,
) {
    SharedTransitionScope {
        Box(it.then(modifier)) {
            content()
        }
    }
}

@Composable
expect fun SharedTransitionScope(
    content: @Composable SharedTransitionScope.(Modifier) -> Unit,
)

interface SharedTransitionScope : LookaheadScope {

    fun Modifier.sharedElementWithCallerManagedVisibility(
        sharedContentState: SharedContentState,
        visible: Boolean,
        renderInOverlayDuringTransition: Boolean = true,
        zIndexInOverlay: Float = 0f,
    ): Modifier

    fun Modifier.sharedElement(
        sharedContentState: SharedContentState,
        animatedVisibilityScope: AnimatedVisibilityScope,
        renderInOverlayDuringTransition: Boolean = true,
        zIndexInOverlay: Float = 0f,
    ): Modifier

    @Composable
    fun rememberSharedContentState(key: Any): SharedContentState

    interface SharedContentState {
        val isMatchFound: Boolean

        val clipPathInOverlay: Path?

        val parentSharedContentState: SharedContentState?
    }
}

@Composable
fun Modifier.trySharedElement(
    key: Any,
    renderInOverlayDuringTransition: Boolean = true,
    zIndexInOverlay: Float = 0f,
): Modifier {
    val animatedVisibilityScope = LocalNavigationAnimatedVisibilityScope.current
    val sharedTransitionScope = LocalNavigationSharedTransitionScope.current

    return this.then(
        if (animatedVisibilityScope == null || sharedTransitionScope == null) {
            Modifier
        } else {
            with(sharedTransitionScope) {
                Modifier.sharedElement(
                    sharedContentState = rememberSharedContentState(key),
                    animatedVisibilityScope = animatedVisibilityScope,
                    renderInOverlayDuringTransition = renderInOverlayDuringTransition,
                    zIndexInOverlay = zIndexInOverlay,
                )
            }
        },
    )
}

@Suppress("ComposeCompositionLocalUsage")
val LocalNavigationAnimatedVisibilityScope: ProvidableCompositionLocal<AnimatedVisibilityScope?> =
    compositionLocalOf { null }

@Suppress("ComposeCompositionLocalUsage")
val LocalNavigationSharedTransitionScope: ProvidableCompositionLocal<SharedTransitionScope?> =
    compositionLocalOf { null }
