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

/**
 * A segment of navigation for an underlying navigation type of [T].
 *
 * By segmenting navigation entries with [segmentingNavigationTransform], subsequent [RenderableNavigationTransform]s
 * can arbitrarily combine segments and their associated panes in place into a new combined segment.
 */
sealed interface NavigationSegment<T> {
    /**
     * The list of all values that were combined into this segment.
     */
    val combinedValues: List<T>

    /**
     * A single segment representing a single [value].
     */
    data class SingleSegment<T>(
        val value: T,
    ) : NavigationSegment<T> {
        override val combinedValues: List<T> = listOf(value)
    }

    /**
     * A combined segment. The resulting [combinedValues] should include all navigation values from other segments that
     * were combined into this one.
     */
    interface CombinedSegment<T> : NavigationSegment<T>
}
