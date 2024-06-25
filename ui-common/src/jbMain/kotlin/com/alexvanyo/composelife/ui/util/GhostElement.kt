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

import androidx.compose.runtime.ProvidableCompositionLocal
import androidx.compose.runtime.compositionLocalOf

/**
 * `true` if the current composition is a "ghost" element.
 *
 * A "ghost" element is a piece of UI that is still visible, but is transient. A ghost piece of UI might be animating
 * out during a crossfade, or measured as part of a shared element transition but not placed.
 *
 * UI should generally be side-effect free and safe to draw repeatedly whenever useful, but in cases where that isn't
 * the case, `LocalGhostElement.current` can be inspected to avoid side-effects in those cases.
 *
 * Providing a new value for `LocalGhostElement` should likely not "reset" the value back to `false`, as a child of
 * a ghost element should always be a ghost element itself.
 */
val LocalGhostElement: ProvidableCompositionLocal<Boolean> = compositionLocalOf { false }
