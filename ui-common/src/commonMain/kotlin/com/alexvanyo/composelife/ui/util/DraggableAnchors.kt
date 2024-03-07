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

package com.alexvanyo.composelife.ui.util

import androidx.compose.foundation.ExperimentalFoundationApi

interface DraggableAnchors<T> {
    val size: Int

    fun closestAnchor(position: Float): T?

    fun closestAnchor(position: Float, searchUpwards: Boolean): T?

    fun hasAnchorFor(value: T): Boolean

    fun maxAnchor(): Float

    fun minAnchor(): Float

    fun positionOf(value: T): Float

    fun forEach(block: (anchor: T, position: Float) -> Unit) = Unit
}

@ExperimentalFoundationApi
expect fun <T> DraggableAnchors<T>.asFoundationDraggableAnchors(
    equalsKey: Any? = null,
): androidx.compose.foundation.gestures.DraggableAnchors<T>

internal interface WithEqualsKey {
    val equalsKey: Any?
}
