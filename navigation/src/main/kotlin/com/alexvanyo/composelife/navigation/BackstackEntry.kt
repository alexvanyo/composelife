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
 * An entry in the backstack.
 *
 * This is a stable pair between an unique [id], and an arbitrary [value] of type [T].
 *
 * [BackstackEntry] is [Stable], meaning that [value] must also be [Stable] as anything observing backstack entries
 * will want to observe if any relevant state changes.
 */
@Stable
class BackstackEntry<T>(
    val value: T,
    val previous: BackstackEntry<T>?,
    override val id: UUID = UUID.randomUUID(),
) : NavigationEntry, Iterable<BackstackEntry<T>> {
    override fun iterator(): Iterator<BackstackEntry<T>> = iterator {
        var current: BackstackEntry<T>? = this@BackstackEntry
        while (current != null) {
            yield(current)
            current = current.previous
        }
    }
}
