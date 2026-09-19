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

import cnames.structs.LeanOracleSession
import com.alexvanyo.composelife.sessionvalue.lean.cinterop.LeanStateSnapshotC
import com.alexvanyo.composelife.sessionvalue.lean.cinterop.lean_oracle_create
import com.alexvanyo.composelife.sessionvalue.lean.cinterop.lean_oracle_free
import com.alexvanyo.composelife.sessionvalue.lean.cinterop.lean_oracle_get_snapshot
import com.alexvanyo.composelife.sessionvalue.lean.cinterop.lean_oracle_step_set_upstream
import com.alexvanyo.composelife.sessionvalue.lean.cinterop.lean_oracle_step_set_value
import kotlinx.cinterop.CPointer
import kotlinx.cinterop.ExperimentalForeignApi
import kotlinx.cinterop.alloc
import kotlinx.cinterop.memScoped
import kotlinx.cinterop.ptr
import kotlinx.cinterop.toKString

/**
 * An in-memory differential oracle running the formal Lean 4 specification via Kotlin/Native C-interop.
 */
@OptIn(ExperimentalForeignApi::class)
class LeanSessionValueOracle(
    upstreamSessionId: Long,
    upstreamValueId: Long,
    upstreamValue: String,
    localSessionId: Long,
) : AutoCloseable {

    private var sessionPtr: CPointer<LeanOracleSession>? = lean_oracle_create(
        upstream_session_id = upstreamSessionId.toULong(),
        upstream_value_id = upstreamValueId.toULong(),
        upstream_value = upstreamValue,
        local_session_id = localSessionId.toULong(),
    )

    fun stepSetValue(value: String, valueId: Long): LeanSnapshot {
        val ptr = checkNotNull(sessionPtr) { "Lean session has already been closed" }
        return memScoped {
            val snap = alloc<LeanStateSnapshotC>()
            lean_oracle_step_set_value(ptr, value, valueId.toULong(), snap.ptr)
            snap.toSnapshot()
        }
    }

    fun stepSetUpstream(
        upstreamSessionId: Long,
        upstreamValueId: Long,
        upstreamValue: String,
        freshLocalSessionId: Long,
    ): LeanSnapshot {
        val ptr = checkNotNull(sessionPtr) { "Lean session has already been closed" }
        return memScoped {
            val snap = alloc<LeanStateSnapshotC>()
            lean_oracle_step_set_upstream(
                ptr,
                upstreamSessionId.toULong(),
                upstreamValueId.toULong(),
                upstreamValue,
                freshLocalSessionId.toULong(),
                snap.ptr,
            )
            snap.toSnapshot()
        }
    }

    fun getSnapshot(): LeanSnapshot {
        val ptr = checkNotNull(sessionPtr) { "Lean session has already been closed" }
        return memScoped {
            val snap = alloc<LeanStateSnapshotC>()
            lean_oracle_get_snapshot(ptr, snap.ptr)
            snap.toSnapshot()
        }
    }

    override fun close() {
        sessionPtr?.let {
            lean_oracle_free(it)
            sessionPtr = null
        }
    }

    private fun LeanStateSnapshotC.toSnapshot(): LeanSnapshot = LeanSnapshot(
        exposedSessionId = exposed_session_id.toLong(),
        exposedValueId = exposed_value_id.toLong(),
        exposedValue = exposed_value?.toKString().orEmpty(),
        isLocalSessionActive = is_local_session_active,
        localSessionId = local_session_id.toLong(),
        preLocalSessionId = pre_local_session_id.toLong(),
        isUpstreamUpToDate = is_upstream_up_to_date,
        lastExpectedSessionId = last_expected_session_id.toLong(),
        lastExpectedValueId = last_expected_value_id.toLong(),
    )
}
