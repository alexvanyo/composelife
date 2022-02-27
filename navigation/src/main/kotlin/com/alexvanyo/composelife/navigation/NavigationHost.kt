package com.alexvanyo.composelife.navigation

import androidx.compose.animation.AnimatedContent
import androidx.compose.animation.AnimatedContentScope
import androidx.compose.animation.ContentTransform
import androidx.compose.animation.ExperimentalAnimationApi
import androidx.compose.animation.core.tween
import androidx.compose.animation.fadeIn
import androidx.compose.animation.fadeOut
import androidx.compose.animation.scaleIn
import androidx.compose.animation.with
import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.key
import androidx.compose.runtime.mutableStateMapOf
import androidx.compose.runtime.saveable.listSaver
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.saveable.rememberSaveableStateHolder
import androidx.compose.ui.Modifier
import java.util.UUID

/**
 * The primary composable for displaying a [NavigationState].
 *
 * This automatically animated transitions between content, which is rendered for the current top-most entry with the
 * id of [NavigationState.currentEntryId] as specified in [content].
 *
 * The state for each entry is independently saved via [rememberSaveableStateHolder], and the corresponding state is
 * cleared when the keys are observed to no longer be in the backstack map.
 */
@OptIn(ExperimentalAnimationApi::class)
@Composable
fun <T : NavigationEntry> NavigationHost(
    navigationState: NavigationState<T>,
    modifier: Modifier = Modifier,
    transitionSpec: AnimatedContentScope<T>.() -> ContentTransform = {
        fadeIn(animationSpec = tween(220, delayMillis = 90)) +
            scaleIn(initialScale = 0.92f, animationSpec = tween(220, delayMillis = 90)) with
            fadeOut(animationSpec = tween(90))
    },
    content: @Composable (T) -> Unit,
) {
    val stateHolder = rememberSaveableStateHolder()
    val allKeys = rememberSaveable(
        saver = listSaver(
            save = { it.keys.toList().map(UUID::toString) },
            restore = {
                mutableStateMapOf<UUID, Unit>().apply {
                    putAll(it.map(UUID::fromString).associateWith {})
                }
            }
        )
    ) { mutableStateMapOf<UUID, Unit>() }

    AnimatedContent(
        targetState = navigationState.entryMap.getValue(navigationState.currentEntryId),
        transitionSpec = transitionSpec,
        modifier = modifier,
    ) { entry ->
        key(entry.id) {
            stateHolder.SaveableStateProvider(key = entry.id) {
                content(entry)
            }
        }
    }

    val keySet = navigationState.entryMap.keys.toSet()

    LaunchedEffect(keySet) {
        allKeys.forEach { (id, _) ->
            // Remove the state for a given key if it doesn't correspond to an entry in the backstack map
            if (id !in keySet) {
                stateHolder.removeState(id)
            }
        }
        // Keep track of the ids we've seen, to know which ones we may need to clear out later.
        allKeys.putAll(keySet.associateWith {})
    }
}
