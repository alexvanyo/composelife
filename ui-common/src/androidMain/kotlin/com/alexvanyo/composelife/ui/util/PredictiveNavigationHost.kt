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

import androidx.compose.animation.core.FiniteAnimationSpec
import androidx.compose.animation.core.Spring
import androidx.compose.animation.core.spring
import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.key
import androidx.compose.runtime.saveable.listSaver
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.saveable.rememberSaveableStateHolder
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.unit.IntSize
import com.alexvanyo.composelife.navigation.BackstackEntry
import com.alexvanyo.composelife.navigation.BackstackState
import com.alexvanyo.composelife.navigation.currentEntry
import com.alexvanyo.composelife.navigation.previousEntry
import com.alexvanyo.composelife.snapshotstateset.mutableStateSetOf
import java.util.UUID

@Composable
@Suppress("LongParameterList")
fun <T> PredictiveNavigationHost(
    predictiveBackState: PredictiveBackState,
    backstackState: BackstackState<T>,
    modifier: Modifier = Modifier,
    contentAlignment: Alignment = Alignment.TopStart,
    contentSizeAnimationSpec: FiniteAnimationSpec<IntSize> = spring(stiffness = Spring.StiffnessMediumLow),
    content: @Composable (BackstackEntry<out T>) -> Unit,
) {
    val stateHolder = rememberSaveableStateHolder()
    val allKeys = rememberSaveable(
        saver = listSaver(
            save = { it.map(UUID::toString) },
            restore = {
                mutableStateSetOf<UUID>().apply {
                    addAll(it.map(UUID::fromString))
                }
            },
        ),
    ) { mutableStateSetOf<UUID>() }

    AnimatedContent(
        targetState = when (predictiveBackState) {
            PredictiveBackState.NotRunning -> TargetState.Single(backstackState.currentEntry)
            is PredictiveBackState.Running -> {
                val previous = backstackState.previousEntry
                if (previous != null) {
                    TargetState.InProgress(
                        current = backstackState.currentEntry,
                        provisional = previous,
                        progress = predictiveBackState.progress,
                    )
                } else {
                    TargetState.Single(backstackState.currentEntry)
                }
            }
        },
        contentAlignment = contentAlignment,
        contentSizeAnimationSpec = contentSizeAnimationSpec,
        modifier = modifier,
    ) { entry ->
        key(entry.id) {
            stateHolder.SaveableStateProvider(key = entry.id) {
                content(entry)
            }
        }
    }

    val keySet = backstackState.entryMap.keys.toSet()

    LaunchedEffect(keySet) {
        // Remove the state for a given key if it doesn't correspond to an entry in the backstack map
        (allKeys - keySet).forEach(stateHolder::removeState)
        // Keep track of the ids we've seen, to know which ones we may need to clear out later.
        allKeys.addAll(keySet)
    }
}
