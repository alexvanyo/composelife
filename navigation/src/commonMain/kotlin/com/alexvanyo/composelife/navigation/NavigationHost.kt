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

package com.alexvanyo.composelife.navigation

import androidx.compose.animation.AnimatedContent
import androidx.compose.animation.AnimatedContentTransitionScope
import androidx.compose.animation.ContentTransform
import androidx.compose.animation.core.tween
import androidx.compose.animation.fadeIn
import androidx.compose.animation.fadeOut
import androidx.compose.animation.scaleIn
import androidx.compose.animation.togetherWith
import androidx.compose.foundation.layout.Box
import androidx.compose.runtime.Composable
import androidx.compose.runtime.CompositionLocalProvider
import androidx.compose.runtime.DisposableEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.movableContentOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.runtime.saveable.rememberSaveableStateHolder
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import com.slack.circuit.retained.CanRetainChecker
import com.slack.circuit.retained.LocalCanRetainChecker
import com.slack.circuit.retained.LocalRetainedStateRegistry
import com.slack.circuit.retained.RetainedStateRegistry
import com.slack.circuit.retained.rememberRetained

/**
 * The primary composable for displaying a [NavigationState].
 *
 * This automatically animated transitions between content, which is rendered for the current top-most entry with the
 * id of [NavigationState.currentEntryId] as specified in [content].
 *
 * The state for each entry is independently saved via [rememberSaveableStateHolder], and the corresponding state is
 * cleared when the keys are observed to no longer be in the backstack map.
 */
@Composable
fun <T : NavigationEntry> NavigationHost(
    navigationState: NavigationState<T>,
    modifier: Modifier = Modifier,
    transitionSpec: AnimatedContentTransitionScope<T>.() -> ContentTransform = {
        (
            fadeIn(animationSpec = tween(220, delayMillis = 90)) +
                scaleIn(initialScale = 0.92f, animationSpec = tween(220, delayMillis = 90))
            )
            .togetherWith(fadeOut(animationSpec = tween(90)))
    },
    contentAlignment: Alignment = Alignment.TopStart,
    content: @Composable (T) -> Unit,
) = NavigationHost(
    navigationState = navigationState,
    modifier = modifier,
    decoration = defaultNavigationDecoration(
        transitionSpec = transitionSpec,
        contentAlignment = contentAlignment,
    ),
    content = content,
)

@Composable
fun <T : NavigationEntry, S : NavigationState<T>> NavigationHost(
    navigationState: S,
    modifier: Modifier = Modifier,
    decoration: NavigationDecoration<T, S>,
    content: @Composable (T) -> Unit,
) {
    val saveableStateHolder = rememberSaveableStateHolder()

    /**
     * Create a [RetainedStateRegistry] for the NavigationHost.
     * This will keep all individual entry's [RetainedStateRegistry]s retained even if they are not composed.
     */
    val retainedStateRegistry = rememberRetained { RetainedStateRegistry() }

    val currentEntryKeySet by rememberUpdatedState(navigationState.entryMap.keys.toSet())

    // Set up a DisposableEffect for each entry key in the backstack to clear a particular entry's state from the
    // retainedStateRegistry when the entry is no longer in the backstack.
    // Without this, entry state would leak and be kept around indefinitely in the case where an entry is removed
    // from the backstack while not currently being rendered.
    currentEntryKeySet.forEach { entryKey ->
        key(entryKey) {
            DisposableEffect(Unit) {
                // Ordering note: This will happen _after_ the entryRetainedStateRegistry's onDispose in
                // due to LIFO ordering of DisposableEffect, so any retained entry state saved there will be cleared.
                onDispose {
                    if (entryKey !in currentEntryKeySet) {
                        retainedStateRegistry.consumeValue(entryKey.toString())
                    }
                }
            }
        }
    }

    Box(
        modifier = modifier,
        propagateMinConstraints = true,
    ) {
        decoration(navigationState) { entry ->
            saveableStateHolder.SaveableStateProvider(key = entry.id) {
                CompositionLocalProvider(
                    LocalRetainedStateRegistry provides retainedStateRegistry,
                    /**
                     * Only retain the entry [RetainedStateRegistry] when it is in the backstack.
                     */
                    LocalCanRetainChecker provides { entry.id in currentEntryKeySet },
                ) {
                    val entryRetainedStateRegistry = rememberRetained(key = entry.id.toString()) {
                        RetainedStateRegistry()
                    }

                    CompositionLocalProvider(
                        LocalRetainedStateRegistry provides entryRetainedStateRegistry,
                        LocalCanRetainChecker provides CanRetainChecker.Always,
                    ) {
                        content(entry)
                    }
                }
            }
        }
    }

    // Set up a DisposableEffect for each entry key in the backstack to clear a particular entry's state from the
    // saveableStateHolder when the entry is no longer in the backstack.
    // Without this, entry state would leak and be kept around indefinitely in the case where an entry is removed
    // from the backstack while not currently being rendered.
    currentEntryKeySet.forEach { entryKey ->
        key(entryKey) {
            DisposableEffect(Unit) {
                // Ordering note: This will happen _before_ the content's onDispose in SaveableStateProvider due to
                // LIFO ordering of DisposableEffect, so the removed entry state saving will be skipped.
                onDispose {
                    if (entryKey !in currentEntryKeySet) {
                        saveableStateHolder.removeState(entryKey)
                    }
                }
            }
        }
    }
}

/**
 * The decoration for screens in the context of navigation.
 *
 * Given the [screen] lambda for rendering a screen for a navigation entry [T], the [NavigationDecoration] should
 * display one (or more) screens based on the current navigation state.
 *
 * This very simplest [NavigationDecoration] just renders the current screen, and the current screen only
 * (see [noopNavigationDecoration]). Most likely, this is not enough: this specifies no navigation transition between
 * screens.
 *
 * The [defaultNavigationDecoration] internally performs an [AnimatedContent] on the current screen, which animates
 * out old screens.
 *
 * It is the responsibility of the [NavigationDecoration] to preserve intrinsic state of the [screen], so that it
 * can be re-parented. In other words, [NavigationDecoration] should use [movableContentOf] if necessary to move
 * screens around to different call sites in order to preserve state.
 */
typealias NavigationDecoration<T, S> = @Composable S.(screen: @Composable (T) -> Unit) -> Unit

/**
 * The default [NavigationDecoration], which uses an [AnimatedContent] to animate between screens, using the given
 * [transitionSpec] and [contentAlignment].
 */
fun <T : NavigationEntry> defaultNavigationDecoration(
    transitionSpec: AnimatedContentTransitionScope<T>.() -> ContentTransform = {
        (
            fadeIn(animationSpec = tween(220, delayMillis = 90)) +
                scaleIn(initialScale = 0.92f, animationSpec = tween(220, delayMillis = 90))
            )
            .togetherWith(fadeOut(animationSpec = tween(90)))
    },
    contentAlignment: Alignment = Alignment.TopStart,
): NavigationDecoration<T, NavigationState<T>> = { screen ->
    val currentScreen by rememberUpdatedState(screen)
    val movableScreens = entryMap.mapValues { (id, entry) ->
        key(id) {
            val currentEntry by rememberUpdatedState(entry)
            remember {
                movableContentOf {
                    currentScreen(currentEntry)
                }
            }
        }
    }

    AnimatedContent(
        targetState = entryMap.getValue(currentEntryId),
        transitionSpec = transitionSpec,
        contentAlignment = contentAlignment,
    ) { entry ->
        key(entry.id) {
            // Fetch and store the movable screen to hold onto while animating out
            val movableScreen = remember { movableScreens.getValue(entry.id) }
            movableScreen()
        }
    }
}

/**
 * The simplest [NavigationDecoration] implementation, which just displays the current screen with a jumpcut.
 */
fun <T : NavigationEntry> noopNavigationDecoration(): NavigationDecoration<T, NavigationState<T>> = { screen ->
    screen(entryMap.getValue(currentEntryId))
}
