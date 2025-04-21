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

package com.alexvanyo.composelife.ui.util

import androidx.compose.runtime.Composable
import androidx.compose.ui.graphics.Path

/**
 * The shape of the window, as expressed in a [Path].
 */
interface WindowShape {

    /**
     * The [Path] describing the shape of the window. This is expressed in window coordinates - components that
     * may match the window coordinate space will need to transform this path into their coordinate space.
     */
    val path: Path
}

@Composable
expect fun currentWindowShape(): WindowShape
