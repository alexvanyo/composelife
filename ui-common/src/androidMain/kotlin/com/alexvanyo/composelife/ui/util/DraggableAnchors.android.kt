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

@ExperimentalFoundationApi
actual fun <T> DraggableAnchors<T>.asFoundationDraggableAnchors(
    equalsKey: Any?,
): androidx.compose.foundation.gestures.DraggableAnchors<T> =
    object : androidx.compose.foundation.gestures.DraggableAnchors<T>, WithEqualsKey {
        override val size: Int
            get() = this@asFoundationDraggableAnchors.size
        override fun closestAnchor(position: Float): T? =
            this@asFoundationDraggableAnchors.closestAnchor(position)
        override fun closestAnchor(position: Float, searchUpwards: Boolean): T? =
            this@asFoundationDraggableAnchors.closestAnchor(position, searchUpwards)
        override fun maxAnchor(): Float =
            this@asFoundationDraggableAnchors.maxAnchor()
        override fun minAnchor(): Float =
            this@asFoundationDraggableAnchors.minAnchor()
        override fun positionOf(value: T): Float =
            this@asFoundationDraggableAnchors.positionOf(value)
        override fun hasAnchorFor(value: T): Boolean =
            this@asFoundationDraggableAnchors.hasAnchorFor(value)
        override fun forEach(block: (anchor: T, position: Float) -> Unit) =
            this@asFoundationDraggableAnchors.forEach(block)

        override val equalsKey: Any? get() = equalsKey

        override fun equals(other: Any?): Boolean =
            other is androidx.compose.foundation.gestures.DraggableAnchors<*> &&
                if (other is WithEqualsKey) {
                    this.equalsKey == other.equalsKey
                } else {
                    this === other
                }
    }
