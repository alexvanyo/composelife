/*
 * Copyright 2025 The Android Open Source Project
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

package com.alexvanyo.composelife.navigation3.scene

import androidx.compose.foundation.layout.Box
import androidx.compose.runtime.Composable
import androidx.compose.runtime.remember
import androidx.compose.ui.Modifier
import androidx.navigation3.runtime.NavEntryDecorator
import com.alexvanyo.composelife.navigation.trySharedElement

/** Returns a [SharedEntryInSceneNavEntryDecorator] that is remembered across recompositions. */
@Composable
internal fun <T : Any> rememberSharedEntryInSceneNavEntryDecorator(): SharedEntryInSceneNavEntryDecorator<T> =
    remember { SharedEntryInSceneNavEntryDecorator() }

/**
 * A [NavEntryDecorator] that wraps each entry in a [Modifier.sharedElement] to allow nav displays
 * to animate arbitrarily place entries in different places in the composable call hierarchy.
 *
 * This should be wrapped around the [SceneSetupNavEntryDecorator].
 */
internal class SharedEntryInSceneNavEntryDecorator<T : Any>: NavEntryDecorator<T>(
    decorate = { entry ->
        Box(
            Modifier.trySharedElement(
                key = entry.contentKey,
            ),
        ) {
            entry.Content()
        }
    },
)
