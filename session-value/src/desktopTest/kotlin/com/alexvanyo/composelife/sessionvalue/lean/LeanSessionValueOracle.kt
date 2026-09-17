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

package com.alexvanyo.composelife.sessionvalue.lean

import com.dshatz.kni.load.BundledLibLoader

/**
 * An in-memory differential oracle running the formal Lean 4 specification via JNI.
 */
class LeanSessionValueOracle(
    upstreamSessionId: Long,
    upstreamValueId: Long,
    upstreamValue: String,
    localSessionId: Long,
) : AutoCloseable {

    private var sessionPtr: Long = create(
        upstreamSessionId = upstreamSessionId,
        upstreamValueId = upstreamValueId,
        upstreamValue = upstreamValue,
        localSessionId = localSessionId,
    )

    fun stepSetValue(value: String, valueId: Long): LeanSnapshot {
        check(sessionPtr != 0L) { "Lean session has already been closed" }
        return nativeStepSetValue(sessionPtr, value, valueId)
    }

    fun stepSetUpstream(
        upstreamSessionId: Long,
        upstreamValueId: Long,
        upstreamValue: String,
        freshLocalSessionId: Long,
    ): LeanSnapshot {
        check(sessionPtr != 0L) { "Lean session has already been closed" }
        return nativeStepSetUpstream(
            sessionPtr,
            upstreamSessionId,
            upstreamValueId,
            upstreamValue,
            freshLocalSessionId,
        )
    }

    fun getSnapshot(): LeanSnapshot {
        check(sessionPtr != 0L) { "Lean session has already been closed" }
        return nativeGetSnapshot(sessionPtr)
    }

    override fun close() {
        if (sessionPtr != 0L) {
            nativeDestroy(sessionPtr)
            sessionPtr = 0L
        }
    }

    companion object {
        init {
            BundledLibLoader.loadBundledLibrary("sessionvalue_lean")
        }

        @JvmStatic
        private external fun create(
            upstreamSessionId: Long,
            upstreamValueId: Long,
            upstreamValue: String,
            localSessionId: Long,
        ): Long

        @JvmStatic
        private external fun nativeStepSetValue(sessionPtr: Long, value: String, valueId: Long): LeanSnapshot

        @JvmStatic
        private external fun nativeStepSetUpstream(
            sessionPtr: Long,
            upstreamSessionId: Long,
            upstreamValueId: Long,
            upstreamValue: String,
            freshLocalId: Long,
        ): LeanSnapshot

        @JvmStatic
        private external fun nativeGetSnapshot(sessionPtr: Long): LeanSnapshot

        @JvmStatic
        private external fun nativeDestroy(sessionPtr: Long)
    }
}
