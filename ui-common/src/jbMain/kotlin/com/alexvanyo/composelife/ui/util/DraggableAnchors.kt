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

    /** The number of anchors */
    val size: Int

    /**
     * Get the anchor position for an associated [anchor]
     *
     * @param anchor The value to look up
     * @return The position of the anchor, or [Float.NaN] if the anchor does not exist
     */
    fun positionOf(anchor: T): Float

    /**
     * Whether there is an anchor position associated with the [anchor]
     *
     * @param anchor The value to look up
     * @return true if there is an anchor for this value, false if there is no anchor for this value
     */
    fun hasPositionFor(anchor: T): Boolean

    /**
     * Find the closest anchor value to the [position].
     *
     * @param position The position to start searching from
     * @return The closest anchor or null if the anchors are empty
     */
    fun closestAnchor(position: Float): T?

    /**
     * Find the closest anchor value to the [position], in the specified direction.
     *
     * @param position The position to start searching from
     * @param searchUpwards Whether to search upwards from the current position or downwards
     * @return The closest anchor or null if the anchors are empty
     */
    fun closestAnchor(position: Float, searchUpwards: Boolean): T?

    /** The smallest anchor position, or [Float.NEGATIVE_INFINITY] if the anchors are empty. */
    fun minPosition(): Float

    /** The biggest anchor position, or [Float.POSITIVE_INFINITY] if the anchors are empty. */
    fun maxPosition(): Float

    /** Get the anchor key at the specified index, or null if the index is out of bounds. */
    fun anchorAt(index: Int): T?

    /**
     * Get the anchor position at the specified index, or [Float.NaN] if the index is out of bounds.
     */
    fun positionAt(index: Int): Float

    /**
     * Iterate over all the anchors and corresponding positions.
     *
     * @param block The action to invoke with the anchor and position
     */
    fun forEach(block: (anchor: T, position: Float) -> Unit)
}

@OptIn(ExperimentalFoundationApi::class)
expect fun <T> DraggableAnchors<T>.asFoundationDraggableAnchors(
    equalsKey: Any? = null,
): androidx.compose.foundation.gestures.DraggableAnchors<T>

internal interface WithEqualsKey {
    val equalsKey: Any?
}
