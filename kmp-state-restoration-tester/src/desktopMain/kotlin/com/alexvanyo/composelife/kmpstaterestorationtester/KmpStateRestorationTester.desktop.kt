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

import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.saveable.SaveableStateRegistry
import androidx.compose.runtime.setValue

private class RestorationRegistryImpl(private val original: SaveableStateRegistry) :
    RestorationRegistry {

    override var shouldEmitChildren by mutableStateOf(true)
        private set
    private var currentRegistry: SaveableStateRegistry = original
    private var savedMap: Map<String, List<Any?>> = emptyMap()

    override fun saveStateAndDisposeChildren() {
        savedMap = currentRegistry.performSave()
        shouldEmitChildren = false
    }

    override fun emitChildrenWithRestoredState() {
        currentRegistry = SaveableStateRegistry(
            restoredValues = savedMap,
            canBeSaved = { original.canBeSaved(it) },
        )
        shouldEmitChildren = true
    }

    override fun consumeRestored(key: String) = currentRegistry.consumeRestored(key)

    override fun registerProvider(key: String, valueProvider: () -> Any?) =
        currentRegistry.registerProvider(key, valueProvider)

    override fun canBeSaved(value: Any) = currentRegistry.canBeSaved(value)

    override fun performSave() = currentRegistry.performSave()
}

internal actual fun RestorationRegistry(
    original: SaveableStateRegistry,
): RestorationRegistry = RestorationRegistryImpl(original)
