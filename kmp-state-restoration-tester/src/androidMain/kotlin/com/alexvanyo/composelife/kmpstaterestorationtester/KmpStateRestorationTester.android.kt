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

package com.alexvanyo.composelife.kmpstaterestorationtester

import android.os.Bundle
import android.os.Parcel
import android.os.Parcelable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.saveable.SaveableStateRegistry
import androidx.compose.runtime.setValue
import com.slack.circuit.retained.RetainedStateRegistry
import com.slack.circuit.retained.RetainedValueProvider

private class RestorationRegistryImpl(
    private val originalSaveableStateRegistry: SaveableStateRegistry,
    private val retainedStateRegistry: RetainedStateRegistry,
) : RestorationRegistry {

    override var shouldEmitChildren by mutableStateOf(true)
        private set
    private var currentSaveableStateRegistry: SaveableStateRegistry = originalSaveableStateRegistry
    private lateinit var savedParcel: Parcel

    override fun saveStateAndDisposeChildren() {
        savedParcel = Parcel.obtain().also {
            currentSaveableStateRegistry.performSave().toBundle().writeToParcel(it, Parcelable.PARCELABLE_WRITE_RETURN_VALUE)
        }
        retainedStateRegistry.saveAll()
        shouldEmitChildren = false
    }

    override fun emitChildrenWithRestoredState() {
        savedParcel.setDataPosition(0)
        val restoredValues = Bundle.CREATOR.createFromParcel(savedParcel).apply {
            classLoader = this@RestorationRegistryImpl.javaClass.classLoader
        }.toMap()
        savedParcel.recycle()
        currentSaveableStateRegistry = SaveableStateRegistry(
            restoredValues = restoredValues,
            canBeSaved = { originalSaveableStateRegistry.canBeSaved(it) },
        )
        shouldEmitChildren = true
    }

    override fun consumeRestored(key: String) = currentSaveableStateRegistry.consumeRestored(key)

    override fun registerProvider(key: String, valueProvider: () -> Any?) =
        currentSaveableStateRegistry.registerProvider(key, valueProvider)

    override fun canBeSaved(value: Any) = currentSaveableStateRegistry.canBeSaved(value)

    override fun performSave() = currentSaveableStateRegistry.performSave()

    override fun consumeValue(key: String): Any? =
        retainedStateRegistry.consumeValue(key)

    override fun forgetUnclaimedValues() =
        retainedStateRegistry.forgetUnclaimedValues()

    override fun registerValue(key: String, valueProvider: RetainedValueProvider): RetainedStateRegistry.Entry =
        retainedStateRegistry.registerValue(key, valueProvider)

    override fun saveAll() = retainedStateRegistry.saveAll()

    override fun saveValue(key: String)= retainedStateRegistry.saveValue(key)
}

internal actual fun RestorationRegistry(
    originalSaveableStateRegistry: SaveableStateRegistry,
    originalRetainedStateRegistry: RetainedStateRegistry,
): RestorationRegistry = RestorationRegistryImpl(originalSaveableStateRegistry, originalRetainedStateRegistry)

// Copied from DisposableSaveableStateRegistry.android.kt
@Suppress("DEPRECATION", "UNCHECKED_CAST")
private fun Bundle.toMap(): Map<String, List<Any?>>? {
    val map = mutableMapOf<String, List<Any?>>()
    this.keySet().forEach { key ->
        val list = getParcelableArrayList<Parcelable?>(key) as ArrayList<Any?>
        map[key] = list
    }
    return map
}

// Copied from DisposableSaveableStateRegistry.android.kt
@Suppress("UNCHECKED_CAST")
private fun Map<String, List<Any?>>.toBundle(): Bundle {
    val bundle = Bundle()
    forEach { (key, list) ->
        val arrayList = if (list is ArrayList<Any?>) list else ArrayList(list)
        bundle.putParcelableArrayList(
            key,
            arrayList as ArrayList<Parcelable?>,
        )
    }
    return bundle
}
