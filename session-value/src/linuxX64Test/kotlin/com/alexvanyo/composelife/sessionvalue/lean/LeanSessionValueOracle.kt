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
import com.alexvanyo.composelife.sessionvalue.lean.cinterop.LeanUuidC
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
import kotlin.uuid.ExperimentalUuidApi
import kotlin.uuid.Uuid

/**
 * An in-memory differential oracle running the formal Lean 4 specification via Kotlin/Native C-interop.
 */
@OptIn(ExperimentalForeignApi::class)
class LeanSessionValueOracle(
    upstreamSessionId: Uuid,
    upstreamValueId: Uuid,
    upstreamValue: String,
    localSessionId: Uuid,
) : AutoCloseable {

    private var sessionPtr: CPointer<LeanOracleSession>? = upstreamSessionId.useULongs { uSessMsb, uSessLsb ->
        upstreamValueId.useULongs { uValMsb, uValLsb ->
            localSessionId.useULongs { locMsb, locLsb ->
                lean_oracle_create(
                    upstream_session_id_msb = uSessMsb,
                    upstream_session_id_lsb = uSessLsb,
                    upstream_value_id_msb = uValMsb,
                    upstream_value_id_lsb = uValLsb,
                    upstream_value = upstreamValue,
                    local_session_id_msb = locMsb,
                    local_session_id_lsb = locLsb,
                )
            }
        }
    }

    fun stepSetValue(value: String, valueId: Uuid): LeanSnapshot {
        val ptr = checkNotNull(sessionPtr) { "Lean session has already been closed" }
        return memScoped {
            val snap = alloc<LeanStateSnapshotC>()
            valueId.useULongs { valIdMsb, valIdLsb ->
                lean_oracle_step_set_value(ptr, value, valIdMsb, valIdLsb, snap.ptr)
            }
            snap.toSnapshot()
        }
    }

    fun stepSetUpstream(
        upstreamSessionId: Uuid,
        upstreamValueId: Uuid,
        upstreamValue: String,
        freshLocalSessionId: Uuid,
    ): LeanSnapshot {
        val ptr = checkNotNull(sessionPtr) { "Lean session has already been closed" }
        return memScoped {
            val snap = alloc<LeanStateSnapshotC>()
            upstreamSessionId.useULongs { uSessMsb, uSessLsb ->
                upstreamValueId.useULongs { uValMsb, uValLsb ->
                    freshLocalSessionId.useULongs { freshIdMsb, freshIdLsb ->
                        lean_oracle_step_set_upstream(
                            ptr,
                            uSessMsb,
                            uSessLsb,
                            uValMsb,
                            uValLsb,
                            upstreamValue,
                            freshIdMsb,
                            freshIdLsb,
                            snap.ptr,
                        )
                    }
                }
            }
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
        exposedSessionId = exposed_session_id.toUuid(),
        exposedValueId = exposed_value_id.toUuid(),
        exposedValue = exposed_value?.toKString().orEmpty(),
        isLocalSessionActive = is_local_session_active,
        localSessionId = local_session_id.toUuid(),
        preLocalSessionId = pre_local_session_id.toUuid(),
        isUpstreamUpToDate = is_upstream_up_to_date,
        lastExpectedSessionId = last_expected_session_id.toUuid(),
        lastExpectedValueId = last_expected_value_id.toUuid(),
    )
}

@OptIn(ExperimentalUuidApi::class)
private inline fun <R> Uuid.useULongs(block: (msb: ULong, lsb: ULong) -> R): R =
    toLongs { msb, lsb -> block(msb.toULong(), lsb.toULong()) }

@OptIn(ExperimentalForeignApi::class, ExperimentalUuidApi::class)
private fun LeanUuidC.toUuid(): Uuid = Uuid.fromLongs(most_significant_bits.toLong(), least_significant_bits.toLong())
