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

/**
 * Represents an API surface that is typically only useful for custom implementations of a
 * [AbstractTraceSink] or a [Track].
 *
 * Any use of a delicate declaration has to be carefully reviewed to make sure it is properly used
 * and does not create problems like memory and resource leaks.
 *
 * Carefully read documentation of any declaration marked as [DelicateTracingApi].
 */
@RequiresOptIn(message = "Marks declarations in the Tracing API that are delicate.")
@Target(AnnotationTarget.CLASS, AnnotationTarget.FUNCTION, AnnotationTarget.PROPERTY)
public annotation class DelicateTracingApi

/**
 * Represents an API surface that is typically only useful for custom context propagation. Carefully
 * read documentation of any declaration marked as [ExperimentalContextPropagation].
 */
@RequiresOptIn(message = "Marks APIs that are highly experimental for context propagation.")
@Target(AnnotationTarget.CLASS, AnnotationTarget.FUNCTION, AnnotationTarget.PROPERTY)
public annotation class ExperimentalContextPropagation

/**
 * Common abstraction for `androidx.tracing.AbstractTraceDriver`.
 */
@Suppress("UnusedPrivateProperty")
expect abstract class AbstractTraceDriver : AutoCloseable {
    protected constructor(sink: AbstractTraceSink, isEnabled: Boolean)

    val sink: AbstractTraceSink
    val isEnabled: Boolean

    abstract val tracer: Tracer
    abstract fun flush()
    abstract override fun close()
}

/**
 * Common abstraction for `androidx.tracing.Tracer`.
 */
expect abstract class Tracer {
    val isEnabled: Boolean

    @ExperimentalContextPropagation
    abstract fun tokenForManualPropagation(): PropagationToken

    @DelicateTracingApi
    abstract fun tokenFromThreadContext(): PropagationToken

    @DelicateTracingApi
    abstract suspend fun tokenFromCoroutineContext(): PropagationToken

    @DelicateTracingApi
    abstract fun beginSectionWithMetadata(
        category: String,
        name: String,
        token: PropagationToken?,
        isRoot: Boolean,
    ): EventMetadataCloseable

    @DelicateTracingApi
    abstract suspend fun beginCoroutineSectionWithMetadata(
        category: String,
        name: String,
        token: PropagationToken?,
        isRoot: Boolean,
    ): EventMetadataCloseable

    abstract fun counter(category: String, name: String): Counter

    @DelicateTracingApi
    abstract fun instant(category: String, name: String): EventMetadataCloseable
}

/**
 * Common abstraction for `androidx.tracing.PropagationToken`.
 */
expect interface PropagationToken {
    @DelicateTracingApi
    fun contextElementOrNull(): CoroutineContext.Element?
}

/**
 * Common abstraction for `androidx.tracing.EventMetadataCloseable`.
 */
@DelicateTracingApi
expect class EventMetadataCloseable {
    var metadata: EventMetadata
    var closeable: AutoCloseable
    var propagationToken: PropagationToken
}

/**
 * Common abstraction for `androidx.tracing.Counter`.
 */
expect abstract class Counter {
    abstract fun name(): String
    abstract fun setValue(value: Long)
    abstract fun setValue(value: Double)
}

/**
 * Common abstraction for `androidx.tracing.EventMetadata`.
 */
@DelicateTracingApi
expect abstract class EventMetadata {
    abstract fun addMetadataEntry(name: String, value: Boolean)
    abstract fun addMetadataEntry(name: String, value: Long)
    abstract fun addMetadataEntry(name: String, value: Double)
    abstract fun addMetadataEntry(name: String, value: String)
    abstract fun addCallStackEntry(name: String, sourceFile: String?, lineNumber: Int)
    abstract fun addCorrelationId(id: Long)
    abstract fun addCorrelationId(id: String)
    abstract fun addCategory(name: String)
    abstract fun dispatchToTraceSink()
}

/**
 * Common abstraction for `androidx.tracing.AbstractTraceSink`.
 */
expect abstract class AbstractTraceSink : AutoCloseable {
    abstract fun enqueue(pooledPacketArray: PooledTracePacketArray)
    abstract fun onDroppedTraceEvent()
    abstract fun flush()
    abstract override fun close()
}

/**
 * Common abstraction for `androidx.tracing.PooledTracePacketArray`.
 */
@DelicateTracingApi
expect class PooledTracePacketArray {
    fun recycle()
}

/**
 * Writes a trace message indicating that a given section of code has begun.
 */
expect inline fun <T> Tracer.trace(
    category: String,
    name: String,
    crossinline block: () -> T,
): T

/**
 * Writes a trace message indicating that a given suspending section of code has begun.
 */
expect suspend inline fun <T> Tracer.traceCoroutine(
    category: String,
    name: String,
    crossinline block: suspend () -> T,
): T

expect val PropagationUnsupportedToken: PropagationToken

@DelicateTracingApi
expect fun createEventMetadataCloseable(
    metadata: EventMetadata,
    closeable: AutoCloseable,
    propagationToken: PropagationToken,
): EventMetadataCloseable
