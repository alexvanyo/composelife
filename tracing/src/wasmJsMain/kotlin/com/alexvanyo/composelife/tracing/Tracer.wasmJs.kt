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

import kotlin.coroutines.CoroutineContext

actual abstract class AbstractTraceDriver protected actual constructor(actual val sink: AbstractTraceSink) :
    AutoCloseable {
    actual abstract val tracer: Tracer
    actual abstract fun flush()
    actual abstract override fun close()
}

actual abstract class Tracer {

    @DelicateTracingApi
    actual abstract fun tokenFromThreadContext(): PropagationToken

    @DelicateTracingApi
    actual abstract suspend fun tokenFromCoroutineContext(): PropagationToken

    @DelicateTracingApi
    actual abstract fun beginSectionWithMetadata(
        category: String,
        name: String,
        token: PropagationToken?,
        isRoot: Boolean,
    ): EventMetadataCloseable

    @DelicateTracingApi
    actual abstract suspend fun beginCoroutineSectionWithMetadata(
        category: String,
        name: String,
        token: PropagationToken?,
        isRoot: Boolean,
    ): EventMetadataCloseable

    actual abstract fun counter(category: String, name: String): Counter

    @DelicateTracingApi
    actual abstract fun writeInstant(category: String, name: String, token: PropagationToken?): EventMetadataCloseable
}

actual interface PropagationToken {
    @DelicateTracingApi
    actual fun contextElementOrNull(): CoroutineContext.Element?
}

@DelicateTracingApi
actual class EventMetadataCloseable(
    actual var metadata: EventMetadata,
    actual var closeable: AutoCloseable,
    actual var propagationToken: PropagationToken,
)

actual interface Counter {
    actual fun name(): String
    actual fun setValue(value: Long)
    actual fun setValue(value: Double)
}

@DelicateTracingApi
actual abstract class EventMetadata {
    actual abstract fun addMetadataEntry(name: String, value: Boolean)
    actual abstract fun addMetadataEntry(name: String, value: Long)
    actual abstract fun addMetadataEntry(name: String, value: Double)
    actual abstract fun addMetadataEntry(name: String, value: String)
    actual abstract fun addCallStackEntry(name: String, sourceFile: String?, lineNumber: Int)
    actual abstract fun addCorrelationId(id: Long)
    actual abstract fun addCorrelationId(id: String)
    actual abstract fun addCategory(name: String)
    actual abstract fun dispatchToTraceSink()
}

actual abstract class AbstractTraceSink : AutoCloseable {
    actual abstract fun enqueue(pooledPacketArray: PooledTracePacketArray)
    actual abstract fun onDroppedTraceEvent()
    actual abstract fun flush()
    actual abstract override fun close()
}

@DelicateTracingApi
actual class PooledTracePacketArray {
    actual fun recycle() = Unit
}

@Suppress("NOTHING_TO_INLINE")
actual inline fun <T> Tracer.trace(category: String, name: String, crossinline block: () -> T): T = block()

actual suspend inline fun <T> Tracer.traceCoroutine(
    category: String,
    name: String,
    crossinline block: suspend () -> T,
): T = block()

private object WasmJsPropagationUnsupportedToken : PropagationToken {
    @DelicateTracingApi
    override fun contextElementOrNull(): CoroutineContext.Element? = null
}

actual val PropagationUnsupportedToken: PropagationToken = WasmJsPropagationUnsupportedToken

@DelicateTracingApi
actual fun createEventMetadataCloseable(
    metadata: EventMetadata,
    closeable: AutoCloseable,
    propagationToken: PropagationToken,
): EventMetadataCloseable = EventMetadataCloseable(
    metadata = metadata,
    closeable = closeable,
    propagationToken = propagationToken,
)

@ExperimentalContextPropagation
actual fun Tracer.tokenForManualPropagation(flowIds: List<Long>): PropagationToken = PropagationUnsupportedToken
