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

        override fun anchorAt(index: Int): T? =
            this@asFoundationDraggableAnchors.anchorAt(index)

        override fun closestAnchor(position: Float): T? =
            this@asFoundationDraggableAnchors.closestAnchor(position)

        override fun closestAnchor(position: Float, searchUpwards: Boolean): T? =
            this@asFoundationDraggableAnchors.closestAnchor(position, searchUpwards)

        override fun maxPosition(): Float =
            this@asFoundationDraggableAnchors.maxPosition()

        override fun minPosition(): Float =
            this@asFoundationDraggableAnchors.minPosition()

        override fun positionAt(index: Int): Float =
            this@asFoundationDraggableAnchors.positionAt(index)

        override fun positionOf(anchor: T): Float =
            this@asFoundationDraggableAnchors.positionOf(anchor)

        override fun hasPositionFor(anchor: T): Boolean =
            this@asFoundationDraggableAnchors.hasPositionFor(anchor)

        override val equalsKey: Any? get() = equalsKey

        override fun equals(other: Any?): Boolean =
            other is androidx.compose.foundation.gestures.DraggableAnchors<*> &&
                other is WithEqualsKey && this.equalsKey == other.equalsKey
    }
