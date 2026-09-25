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

import lean.mod_l_SessionValue_Bridge
import lean.runtime.LeanCtor
import lean.runtime.LeanObject
import lean.runtime.LeanString
import kotlin.uuid.ExperimentalUuidApi
import kotlin.uuid.Uuid

/**
 * An in-memory differential oracle running the formal Lean 4 specification via JVM bytecode.
 *
 * The Lean `SessionValue/Bridge.lean` module is compiled to a JVM `.class` file by the custom
 * Lean 4 JVM backend (`lean --jvm=...`) and packaged into a JAR on the `jvmTest` classpath.
 * This oracle invokes the Lean oracle functions via direct static method calls on [mod_l_SessionValue_Bridge].
 */
@OptIn(ExperimentalUuidApi::class)
class LeanSessionValueOracle(
    upstreamSessionId: Uuid,
    upstreamValueId: Uuid,
    upstreamValue: String,
    localSessionId: Uuid,
) {

    // Mutable oracle state: the current Lean State and the last expected SessionValue.
    private var state: LeanObject?
    private var lastExp: LeanObject?

    init {
        val pair = mod_l_SessionValue_Bridge.f_SessionValue_oracleInit(
            upstreamSessionId.toLeanUuid(),
            upstreamValueId.toLeanUuid(),
            LeanString.of(upstreamValue),
            localSessionId.toLeanUuid(),
        ) as LeanCtor
        // oracleInit returns State String × SessionValue String
        state = pair.getObj(0)
        lastExp = pair.getObj(1)
    }

    fun stepSetValue(value: String, valueId: Uuid): LeanSnapshot {
        val pair = mod_l_SessionValue_Bridge.f_SessionValue_oracleStepSetValue(
            state,
            LeanString.of(value),
            valueId.toLeanUuid(),
        ) as LeanCtor
        // oracleStepSetValue returns State String × SessionValue String
        state = pair.getObj(0)
        lastExp = pair.getObj(1)
        return makeSnapshot()
    }

    fun stepSetUpstream(
        upstreamSessionId: Uuid,
        upstreamValueId: Uuid,
        upstreamValue: String,
        freshLocalSessionId: Uuid,
    ): LeanSnapshot {
        val nextState = mod_l_SessionValue_Bridge.f_SessionValue_oracleStepSetUpstream(
            state,
            upstreamSessionId.toLeanUuid(),
            upstreamValueId.toLeanUuid(),
            LeanString.of(upstreamValue),
            freshLocalSessionId.toLeanUuid(),
        ) as LeanCtor
        // oracleStepSetUpstream returns State String × SessionValue String
        state = nextState.getObj(0)
        lastExp = nextState.getObj(1)
        return makeSnapshot()
    }

    fun getSnapshot(): LeanSnapshot = makeSnapshot()

    private fun makeSnapshot(): LeanSnapshot {
        val snap = mod_l_SessionValue_Bridge.f_SessionValue_oracleMakeSnapshot(
            state,
            lastExp,
        ) as LeanCtor
        return snap.toSnapshot()
    }

    /**
     * Decodes a [LeanCtor] produced by `oracleMakeSnapshot` into a [LeanSnapshot].
     *
     * Layout of the Lean `StateSnapshot` structure (verified via javap + Bridge.lean):
     * - objs[0]: exposedSessionId (Uuid LeanCtor)
     * - objs[1]: exposedValueId (Uuid LeanCtor)
     * - objs[2]: exposedValue (LeanString)
     * - objs[3]: localSessionId (Uuid LeanCtor)
     * - objs[4]: preLocalSessionId (Uuid LeanCtor)
     * - objs[5]: lastExpectedSessionId (Uuid LeanCtor)
     * - objs[6]: lastExpectedValueId (Uuid LeanCtor)
     * - scalars[0]: isLocalSessionActive (Bool: 0 = false, 1 = true)
     * - scalars[1]: isUpstreamUpToDate (Bool: 0 = false, 1 = true)
     */
    private fun LeanCtor.toSnapshot(): LeanSnapshot = LeanSnapshot(
        exposedSessionId = (getObj(0) as LeanCtor).toUuid(),
        exposedValueId = (getObj(1) as LeanCtor).toUuid(),
        exposedValue = (getObj(2) as LeanString).toString(),
        localSessionId = (getObj(3) as LeanCtor).toUuid(),
        preLocalSessionId = (getObj(4) as LeanCtor).toUuid(),
        lastExpectedSessionId = (getObj(5) as LeanCtor).toUuid(),
        lastExpectedValueId = (getObj(6) as LeanCtor).toUuid(),
        isLocalSessionActive = getScalar(0) != 0L,
        isUpstreamUpToDate = getScalar(1) != 0L,
    )
}

/**
 * Converts a Kotlin [Uuid] to a Lean `Uuid` constructor object.
 *
 * Lean `structure Uuid where mostSignificantBits : UInt64; leastSignificantBits : UInt64`
 * compiles to a [LeanCtor] with tag=0, no obj fields, and 2 packed UInt64 scalar fields.
 */
@OptIn(ExperimentalUuidApi::class)
private fun Uuid.toLeanUuid(): LeanCtor = toLongs { msb, lsb ->
    val ctor = LeanCtor.alloc(0, 0, 2)
    ctor.setScalar(0, msb)
    ctor.setScalar(1, lsb)
    ctor
}

/** Converts a Lean `Uuid` [LeanCtor] back to a Kotlin [Uuid]. */
@OptIn(ExperimentalUuidApi::class)
private fun LeanCtor.toUuid(): Uuid = Uuid.fromLongs(getScalar(0), getScalar(1))
