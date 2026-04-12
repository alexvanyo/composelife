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

import androidx.tracing.AbstractTraceSink
import androidx.tracing.PooledTracePacketArray
import androidx.tracing.TraceContext

private class NoOpSink : AbstractTraceSink() {
    override fun enqueue(pooledPacketArray: PooledTracePacketArray) {
        pooledPacketArray.recycle()
    }
    override fun onDroppedTraceEvent() = Unit
    override fun flush() = Unit
    override fun close() = Unit
}

/**
 * A [AbstractTraceDriver] that does nothing.
 */
actual class TestTraceDriver actual constructor() : AbstractTraceDriver(
    sink = NoOpSink(),
    isEnabled = false,
) {
    private val traceContext = TraceContext(sink, isEnabled)

    override val tracer: Tracer = traceContext.createTracer()

    override fun flush() = Unit
    override fun close() {
        traceContext.close()
    }
}
