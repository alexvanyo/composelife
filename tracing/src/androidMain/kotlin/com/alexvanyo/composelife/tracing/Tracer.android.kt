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

@file:OptIn(
    com.alexvanyo.composelife.tracing.DelicateTracingApi::class,
    androidx.tracing.DelicateTracingApi::class,
)

package com.alexvanyo.composelife.tracing

actual typealias AbstractTraceDriver = androidx.tracing.AbstractTraceDriver

actual typealias Tracer = androidx.tracing.Tracer

actual typealias PropagationToken = androidx.tracing.PropagationToken

actual typealias EventMetadataCloseable = androidx.tracing.EventMetadataCloseable

actual typealias Counter = androidx.tracing.Counter

actual typealias EventMetadata = androidx.tracing.EventMetadata

actual typealias AbstractTraceSink = androidx.tracing.AbstractTraceSink

actual typealias PooledTracePacketArray = androidx.tracing.PooledTracePacketArray

@Suppress("NOTHING_TO_INLINE")
actual inline fun <T> Tracer.trace(category: String, name: String, crossinline block: () -> T): T =
    this.trace(category, name, block = block)

actual suspend inline fun <T> Tracer.traceCoroutine(
    category: String,
    name: String,
    crossinline block: suspend () -> T,
): T = this.traceCoroutine(category, name, block = block)

actual val PropagationUnsupportedToken: PropagationToken = androidx.tracing.PropagationUnsupportedToken

@DelicateTracingApi
actual fun createEventMetadataCloseable(
    metadata: EventMetadata,
    closeable: AutoCloseable,
    propagationToken: PropagationToken,
): EventMetadataCloseable = androidx.tracing.EventMetadataCloseable(
    metadata = metadata,
    closeable = closeable,
    propagationToken = propagationToken,
)
