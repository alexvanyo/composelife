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

package com.alexvanyo.composelife.snapshotstateset

import androidx.compose.runtime.Stable
import androidx.compose.runtime.mutableStateMapOf
import androidx.compose.runtime.snapshots.SnapshotStateMap
import androidx.compose.runtime.snapshots.StateObject

/**
 * An implementation of [MutableSet] that can be observed and snapshot. This is the result type
 * created by [mutableStateSetOf].
 *
 * This class closely implements the same semantics as [HashSet].
 *
 * This class is backed by a [mutableStateMapOf].
 *
 * @see mutableStateSetOf
 */
@Stable
class SnapshotStateSet<T> private constructor(
    private val delegateSnapshotStateMap: SnapshotStateMap<T, Unit>,
) : MutableSet<T> by delegateSnapshotStateMap.keys, StateObject by delegateSnapshotStateMap {
    constructor() : this(delegateSnapshotStateMap = mutableStateMapOf())

    override fun add(element: T): Boolean =
        delegateSnapshotStateMap.put(element, Unit) == null

    override fun addAll(elements: Collection<T>): Boolean =
        elements.map(::add).any()
}

/**
 * Create a instance of [MutableSet]<T> that is observable and can be snapshot.
 */
fun <T> mutableStateSetOf() = SnapshotStateSet<T>()

/**
 * Create an instance of [MutableSet]<T> from a collection that is observable and can be
 * snapshot.
 */
fun <T> Collection<T>.toMutableStateSet() = SnapshotStateSet<T>().also { it.addAll(this) }
