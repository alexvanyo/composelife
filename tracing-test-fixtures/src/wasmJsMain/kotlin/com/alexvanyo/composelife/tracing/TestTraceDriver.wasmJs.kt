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

@file:OptIn(DelicateTracingApi::class)

package com.alexvanyo.composelife.tracing

private object WasmJsEmptyEventMetadata : EventMetadata() {
    override fun addMetadataEntry(name: String, value: Boolean) = Unit
    override fun addMetadataEntry(name: String, value: Long) = Unit
    override fun addMetadataEntry(name: String, value: Double) = Unit
    override fun addMetadataEntry(name: String, value: String) = Unit
    override fun addCallStackEntry(name: String, sourceFile: String?, lineNumber: Int) = Unit
    override fun addCorrelationId(id: Long) = Unit
    override fun addCorrelationId(id: String) = Unit
    override fun addCategory(name: String) = Unit
    override fun dispatchToTraceSink() = Unit
}

private object WasmJsEmptyCloseable : AutoCloseable {
    override fun close() = Unit
}

private fun createWasmJsEventMetadataCloseable(): EventMetadataCloseable = createEventMetadataCloseable(
    metadata = WasmJsEmptyEventMetadata,
    closeable = WasmJsEmptyCloseable,
    propagationToken = PropagationUnsupportedToken,
)

private object WasmJsEmptyTraceSink : AbstractTraceSink() {
    override fun enqueue(pooledPacketArray: PooledTracePacketArray) {
        pooledPacketArray.recycle()
    }
    override fun onDroppedTraceEvent() = Unit
    override fun flush() = Unit
    override fun close() = Unit
}

actual class TestTraceDriver actual constructor() :
    AbstractTraceDriver(
        sink = WasmJsEmptyTraceSink,
    ) {
    actual override val tracer: Tracer = object : Tracer() {
        @ExperimentalContextPropagation
        override fun tokenForManualPropagation(): PropagationToken = PropagationUnsupportedToken

        override fun tokenFromThreadContext(): PropagationToken = PropagationUnsupportedToken

        override suspend fun tokenFromCoroutineContext(): PropagationToken = PropagationUnsupportedToken

        override fun beginSectionWithMetadata(
            category: String,
            name: String,
            token: PropagationToken?,
            isRoot: Boolean,
        ): EventMetadataCloseable = createWasmJsEventMetadataCloseable()

        override suspend fun beginCoroutineSectionWithMetadata(
            category: String,
            name: String,
            token: PropagationToken?,
            isRoot: Boolean,
        ): EventMetadataCloseable = createWasmJsEventMetadataCloseable()

        override fun counter(category: String, name: String): Counter = object : Counter {
            override fun name(): String = name
            override fun setValue(value: Long) = Unit
            override fun setValue(value: Double) = Unit
        }

        override fun instant(category: String, name: String): EventMetadataCloseable =
            createWasmJsEventMetadataCloseable()
    }

    actual override fun flush() = Unit
    actual override fun close() = Unit
}
