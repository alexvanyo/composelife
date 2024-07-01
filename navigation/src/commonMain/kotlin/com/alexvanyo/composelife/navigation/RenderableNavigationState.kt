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

package com.alexvanyo.composelife.navigation

import androidx.compose.runtime.Composable
import com.benasher44.uuid.Uuid

class RenderableNavigationState<T : NavigationEntry, S : NavigationState<T>>(
    val navigationState: S,
    val renderablePanes: Map<Uuid, @Composable () -> Unit>,
)

/**
 * A navigation transform from a [RenderableNavigationState] of [T1] and [S1] into a
 * [RenderableNavigationState] of [T2] and [S2].
 */
typealias RenderableNavigationTransform<T1, S1, T2, S2> =
    @Composable (RenderableNavigationState<T1, S1>) -> RenderableNavigationState<T2, S2>
