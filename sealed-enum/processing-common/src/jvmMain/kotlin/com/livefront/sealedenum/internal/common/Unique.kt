/*
 * Copyright 2020 Livefront
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

package com.livefront.sealedenum.internal.common

/**
 * Returns true if and only if all elements of the [Array] are unique based on the key computed by the [selector].
 *
 * This is logically equivalent to checking if [Array.distinctBy] made the array smaller, but is more efficient
 * due to short-circuiting.
 */
public fun <T, K> Array<T>.areUniqueBy(selector: (T) -> K): Boolean {
    val set = mutableSetOf<K>()
    for (e in this) {
        if (!set.add(selector(e))) {
            return false
        }
    }
    return true
}

/**
 * Returns true if and only if all elements of the [Iterable] are unique based on the key computed by the [selector].
 *
 * This is logically equivalent to checking if [Iterable.distinctBy] made the array smaller, but is more efficient
 * due to short-circuiting.
 */
public fun <T, K> Iterable<T>.areUniqueBy(selector: (T) -> K): Boolean {
    val set = mutableSetOf<K>()
    for (e in this) {
        if (!set.add(selector(e))) {
            return false
        }
    }
    return true
}
