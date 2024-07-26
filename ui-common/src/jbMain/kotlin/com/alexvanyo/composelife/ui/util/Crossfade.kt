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

import androidx.compose.runtime.Composable
import androidx.compose.ui.Modifier

/**
 * A version of Crossfade that can animate between [TargetState]s, a target of either one state or
 * between two states.
 */
@Composable
fun <T> Crossfade(
    targetState: TargetState<T, *>,
    modifier: Modifier = Modifier,
    content: @Composable (T) -> Unit,
) = AnimatedContent(
    targetState = targetState,
    modifier = modifier,
    content = content,
    animateInternalContentSizeChanges = false,
)
