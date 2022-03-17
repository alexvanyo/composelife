/*
 * Copyright 2022 The Android Open Source Project
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

import androidx.compose.runtime.Stable
import java.util.UUID

/**
 * A navigation state for destinations of type [T].
 *
 * A navigation state consists of [entryMap], which represents all known entries that may be returned to at some point.
 *
 * The [currentEntryId] acts as a pointer to the navigation entry to currently display.
 */
@Stable
interface NavigationState<T : NavigationEntry> {

    /**
     * A map of all entries, keyed by their [NavigationEntry.id]. This should contain all previous entries that may
     * be returned to at some point.
     */
    val entryMap: Map<UUID, T>

    /**
     * The id of the current entry. This acts a pointer into [entryMap].
     */
    val currentEntryId: UUID
}

/**
 * The current entry of this [NavigationState], based on the [NavigationState.currentEntryId].
 */
val <T : NavigationEntry> NavigationState<T>.currentEntry: T
    get() = entryMap.getValue(currentEntryId)
