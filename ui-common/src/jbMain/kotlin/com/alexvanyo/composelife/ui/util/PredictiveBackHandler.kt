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

@file:Suppress("MatchingDeclarationName", "Filename")

package com.alexvanyo.composelife.ui.util

import androidx.compose.runtime.Composable
import androidx.compose.runtime.collectAsState
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.saveable.rememberSerializable
import androidx.compose.runtime.setValue
import androidx.navigationevent.NavigationEvent
import androidx.navigationevent.NavigationEventInfo
import androidx.navigationevent.NavigationEventTransitionState
import androidx.navigationevent.compose.LocalNavigationEventDispatcherOwner
import androidx.navigationevent.compose.NavigationBackHandler
import androidx.navigationevent.compose.rememberNavigationEventState
import kotlinx.serialization.serializer
import kotlin.uuid.Uuid

/**
 * The state describing a one-shot back state, with use in a [CompletablePredictiveBackStateHandler].
 *
 * Because the back handler can only be used once there are three states that [CompletablePredictiveBackState] can
 * be in:
 *
 * - [NotRunning]
 * - [Running], which can happen on API 34 and above if a predictive back is in progress.
 * - [Completed]
 */
sealed interface CompletablePredictiveBackState {
    /**
     * There is no predictive back ongoing, and the back has not been completed.
     */
    data object NotRunning : CompletablePredictiveBackState

    /**
     * There is an ongoing predictive back animation, with the given [progress].
     */
    data class Running(
        val touchX: Float,
        val touchY: Float,
        val progress: Float,
        val backEventEdge: BackEventEdge,
    ) : CompletablePredictiveBackState

    /**
     * The back has completed.
     */
    data object Completed : CompletablePredictiveBackState
}

sealed interface BackEventEdge {
    data object Left : BackEventEdge
    data object Right : BackEventEdge
    data object None : BackEventEdge
}

@Composable
fun rememberCompletablePredictiveBackStateHolder(): CompletablePredictiveBackStateHolder {
    val id = rememberSerializable(serializer = serializer()) { Uuid.random() }

    val navigationEventDispatcherOwner =
        requireNotNull(LocalNavigationEventDispatcherOwner.current)

    val navigationEventHistory by
        navigationEventDispatcherOwner.navigationEventDispatcher.history
            .collectAsState()
    val currentInfo = navigationEventHistory.mergedHistory.getOrNull(navigationEventHistory.currentIndex)
    val preCompletedNavigationEventTransitionState =
        if (currentInfo is CompletablePredictiveBackStateInfo && currentInfo.id == id) {
            navigationEventDispatcherOwner.navigationEventDispatcher.transitionState
                .collectAsState().value
        } else {
            NavigationEventTransitionState.Idle
        }

    val preCompletedState =
        when (preCompletedNavigationEventTransitionState) {
            NavigationEventTransitionState.Idle -> CompletablePredictiveBackState.NotRunning
            is NavigationEventTransitionState.InProgress -> CompletablePredictiveBackState.Running(
                touchX = preCompletedNavigationEventTransitionState.latestEvent.touchX,
                touchY = preCompletedNavigationEventTransitionState.latestEvent.touchY,
                progress = preCompletedNavigationEventTransitionState.latestEvent.progress,
                backEventEdge = when (preCompletedNavigationEventTransitionState.latestEvent.swipeEdge) {
                    NavigationEvent.EDGE_LEFT -> BackEventEdge.Left
                    NavigationEvent.EDGE_RIGHT -> BackEventEdge.Right
                    else -> BackEventEdge.None
                },
            )
        }
    val currentPreCompletedState by rememberUpdatedState(preCompletedState)

    var isCompleted by rememberSaveable { mutableStateOf(false) }

    return remember {
        object : CompletablePredictiveBackStateHolderImpl {
            override val id = id

            override var isCompleted: Boolean
                get() = isCompleted
                set(value) {
                    isCompleted = value
                }

            override val value: CompletablePredictiveBackState
                get() = if (isCompleted) {
                    CompletablePredictiveBackState.Completed
                } else {
                    currentPreCompletedState
                }
        }
    }
}

sealed interface CompletablePredictiveBackStateHolder {
    val value: CompletablePredictiveBackState
}

internal interface CompletablePredictiveBackStateHolderImpl : CompletablePredictiveBackStateHolder {
    val id: Uuid

    var isCompleted: Boolean
}

@Composable
fun CompletablePredictiveBackStateHandler(
    completablePredictiveBackStateHolder: CompletablePredictiveBackStateHolder,
    enabled: Boolean,
    onBack: () -> Unit,
) {
    // Safely update the current `onBack` lambda when a new one is provided
    val currentOnBack by rememberUpdatedState(onBack)

    key(completablePredictiveBackStateHolder) {
        when (completablePredictiveBackStateHolder) {
            is CompletablePredictiveBackStateHolderImpl -> Unit
        }
        NavigationBackHandler(
            state = rememberNavigationEventState(
                currentInfo = CompletablePredictiveBackStateInfo(
                    id = completablePredictiveBackStateHolder.id,
                ),
            ),
            isBackEnabled = enabled &&
                completablePredictiveBackStateHolder.value !is CompletablePredictiveBackState.Completed,
            onBackCompleted = {
                completablePredictiveBackStateHolder.isCompleted = true
                currentOnBack()
            },
        )
    }
}

private data class CompletablePredictiveBackStateInfo(
    val id: Uuid,
) : NavigationEventInfo()
