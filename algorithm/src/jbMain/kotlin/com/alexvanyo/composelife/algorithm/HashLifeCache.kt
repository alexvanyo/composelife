/*
 * Copyright 2026 The Android Open Source Project
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

package com.alexvanyo.composelife.algorithm

import androidx.collection.LongIntMap
import androidx.collection.MutableLongIntMap
import androidx.collection.MutableLongLongMap
import androidx.collection.MutableObjectLongMap
import androidx.collection.ObjectLongMap
import androidx.collection.mutableLongIntMapOf
import androidx.collection.mutableLongLongMapOf
import androidx.collection.mutableObjectLongMapOf
import com.alexvanyo.composelife.model.MacroCell

internal fun interface Equivalence<in T> {
    fun isEquivalent(a: T, b: T): Boolean

    fun hash(value: T): Int = value.hashCode()

    class Wrapper<T>(private val equivalence: Equivalence<T>, val value: T) {
        @Suppress("UNCHECKED_CAST")
        override fun equals(other: Any?): Boolean = other is Wrapper<*> &&
            other.equivalence === equivalence &&
            equivalence.isEquivalent(value, (other as Wrapper<T>).value)

        override fun hashCode(): Int = equivalence.hash(value)
    }
}

internal fun <T> Equivalence<T>.wrap(value: T): Equivalence.Wrapper<T> = Equivalence.Wrapper(this, value)

internal val canonicalCellNodeEquivalence: Equivalence<MacroCell.CellNode> =
    Equivalence { a: MacroCell.CellNode, b: MacroCell.CellNode ->
        a.level() == b.level() && a.nw === b.nw && a.ne === b.ne && a.sw === b.sw && a.se === b.se
    }

internal class Cache<K, V>(private val load: (K) -> V, private val getGenerationIndex: () -> Long) {
    private val mutableMap: MutableMap<K, V> = mutableMapOf()
    val map: Map<K, V> get() = mutableMap

    private val lastAccessedGenerationMap: MutableMap<K, Long> = mutableMapOf()

    operator fun get(key: K): V = mutableMap.getOrPut(key) { load(key) }.also {
        lastAccessedGenerationMap[key] = getGenerationIndex()
    }

    fun prune(oldestGenerationToKeep: Long) {
        val iterator = lastAccessedGenerationMap.iterator()
        while (iterator.hasNext()) {
            val mutableEntry = iterator.next()
            if (mutableEntry.value < oldestGenerationToKeep) {
                mutableMap.remove(mutableEntry.key)
                iterator.remove()
            }
        }
    }
}

internal class ObjectLongCache<K>(private val load: (K) -> ULong, private val getGenerationIndex: () -> Long) {
    private val mutableMap: MutableObjectLongMap<K> = mutableObjectLongMapOf()
    val map: ObjectLongMap<K> get() = mutableMap

    private val lastAccessedGenerationMap: MutableObjectLongMap<K> = mutableObjectLongMapOf()

    operator fun get(key: K): ULong = mutableMap.getOrPut(key) { load(key).toLong() }.toULong().also {
        lastAccessedGenerationMap[key] = getGenerationIndex()
    }

    fun prune(oldestGenerationToKeep: Long) {
        lastAccessedGenerationMap.removeIf { key, value ->
            (value < oldestGenerationToKeep).also {
                if (it) {
                    mutableMap.remove(key)
                }
            }
        }
    }
}

internal class LongIntCache(private val load: (ULong) -> Int, private val getGenerationIndex: () -> Long) {
    private val mutableMap: MutableLongIntMap = mutableLongIntMapOf()
    val map: LongIntMap get() = mutableMap

    private val lastAccessedGenerationMap: MutableLongLongMap = mutableLongLongMapOf()

    operator fun get(key: ULong): Int = mutableMap.getOrPut(key.toLong()) { load(key) }.also {
        lastAccessedGenerationMap[key.toLong()] = getGenerationIndex()
    }

    fun prune(oldestGenerationToKeep: Long) {
        lastAccessedGenerationMap.removeIf { key, value ->
            (value < oldestGenerationToKeep).also {
                if (it) {
                    mutableMap.remove(key)
                }
            }
        }
    }
}
