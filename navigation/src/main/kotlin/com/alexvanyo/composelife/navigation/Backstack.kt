package com.alexvanyo.composelife.navigation

import androidx.activity.compose.BackHandler
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
 * The primary composable for displaying a [Backstack].
 *
 * This automatically animated transitions between content, which is rendered for the current top-most entry as
 * specified in [content].
 *
 * The state for each entry is independently saved via [rememberSaveableStateHolder], and the corresponding state is
 * cleared when the keys are observed to no longer be in the backstack.
 *
 * If the state should be kept anyway for a destination not on the backstack (say, for animation or to support
 * multiple backstacks) pass those ids in [idsToKeep] and the state won't be cleared.
 *
 * Note that [backstack] must not be empty. If it would be, avoid calling this composable.
 */
@OptIn(ExperimentalAnimationApi::class)
@Composable
fun <T> Backstack(
    backstack: Backstack<T>,
    modifier: Modifier = Modifier,
    idsToKeep: Set<UUID> = emptySet(),
    transitionSpec: AnimatedContentScope<BackstackEntry<T>>.() -> ContentTransform = {
        fadeIn(animationSpec = tween(220, delayMillis = 90)) +
            scaleIn(initialScale = 0.92f, animationSpec = tween(220, delayMillis = 90)) with
            fadeOut(animationSpec = tween(90))
    },
    content: @Composable (T) -> Unit,
) {
    require(backstack.isNotEmpty())

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
        targetState = backstack.last(),
        transitionSpec = transitionSpec,
        modifier = modifier,
    ) { entry ->
        key(entry.id) {
            stateHolder.SaveableStateProvider(key = entry.id) {
                content(entry.value)
            }
        }
    }

    LaunchedEffect(backstack, idsToKeep) {
        val backstackKeys = backstack.map { it.id }.toSet()
        allKeys.forEach { (id, _) ->
            // Remove the state for a given key if it doesn't correspond to an entry in the backstack and it isn't
            // in idsToKeep
            if (id !in backstackKeys && id !in idsToKeep) {
                stateHolder.removeState(id)
            }
        }
        // Keep track of the ids we've seen, to know which ones we may need to clear out later.
        allKeys.putAll(backstackKeys.associateWith {})
    }
}

/**
 * An appropriate [BackHandler] for this backstack.
 *
 * The [BackHandler] will only be present if the size of the [MutableBackstack] is more than one, and can be disabled
 * via the parameter.
 */
val <T> MutableBackstack<T>.backstackBackHandler: @Composable (enabled: Boolean) -> Unit
    get() = { enabled ->
        if (size > 1) {
            BackHandler(enabled = enabled) {
                popBackstack()
            }
        }
    }
