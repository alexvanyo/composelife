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

import lean.runtime.LeanCtor
import lean.runtime.LeanObject
import lean.runtime.LeanString
import java.lang.reflect.Method
import kotlin.uuid.ExperimentalUuidApi
import kotlin.uuid.Uuid

/**
 * An in-memory differential oracle running the formal Lean 4 specification via JVM bytecode.
 *
 * The Lean `SessionValue/Bridge.lean` module is compiled to a JVM `.class` file by the custom
 * Lean 4 JVM backend (`lean --jvm=...`). This oracle loads that class at runtime and invokes
 * the exported oracle functions as static methods via reflection, using the Lean KMP runtime
 * types ([LeanCtor], [LeanString]) to marshal arguments and results.
 *
 * The class and method names are determined by the Lean JVM name mangling convention
 * (verified via `javap`).
 */
@OptIn(ExperimentalUuidApi::class)
class LeanSessionValueOracle(
    upstreamSessionId: Uuid,
    upstreamValueId: Uuid,
    upstreamValue: String,
    localSessionId: Uuid,
) : AutoCloseable {

    // Reflect into the Lean-generated class once per oracle instance.
    private val bridgeClass: Class<*> = Class.forName(BRIDGE_CLASS_NAME)

    private val oracleInitMethod: Method = bridgeClass.getMethod(
        ORACLE_INIT_METHOD,
        LeanObject::class.java,
        LeanObject::class.java,
        LeanObject::class.java,
        LeanObject::class.java,
    )

    private val stepSetValueMethod: Method = bridgeClass.getMethod(
        STEP_SET_VALUE_METHOD,
        LeanObject::class.java,
        LeanObject::class.java,
        LeanObject::class.java,
    )

    private val stepSetUpstreamMethod: Method = bridgeClass.getMethod(
        STEP_SET_UPSTREAM_METHOD,
        LeanObject::class.java,
        LeanObject::class.java,
        LeanObject::class.java,
        LeanObject::class.java,
        LeanObject::class.java,
    )

    private val makeSnapshotMethod: Method = bridgeClass.getMethod(
        MAKE_SNAPSHOT_METHOD,
        LeanObject::class.java,
        LeanObject::class.java,
    )

    // Mutable oracle state: the current Lean State and the last expected SessionValue.
    private var state: LeanObject?
    private var lastExp: LeanObject?

    init {
        val pair = oracleInitMethod.invoke(
            null,
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
        val currentState = checkNotNull(state) { "Lean session has already been closed" }
        val pair = stepSetValueMethod.invoke(
            null,
            currentState,
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
        val currentState = checkNotNull(state) { "Lean session has already been closed" }
        val nextState = stepSetUpstreamMethod.invoke(
            null,
            currentState,
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

    override fun close() {
        state = null
        lastExp = null
    }

    private fun makeSnapshot(): LeanSnapshot {
        val currentState = checkNotNull(state) { "Lean session has already been closed" }
        val currentLastExp = checkNotNull(lastExp) { "Lean session has already been closed" }
        val snap = makeSnapshotMethod.invoke(null, currentState, currentLastExp) as LeanCtor
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

    companion object {
        /**
         * JVM class name generated by the Lean JVM backend for `SessionValue/Bridge.lean`.
         * The module name `SessionValue.Bridge` is mangled to `l_SessionValue_Bridge`
         * and prefixed with `lean.mod_` (per [Lean.Compiler.LCNF.JVM.toJVMClassName]).
         *
         * Verified via: `javap -p Bridge.class`
         */
        private const val BRIDGE_CLASS_NAME = "lean.mod_l_SessionValue_Bridge"

        // The Lean function names (not @[export] names) are mangled with the `f_` prefix.
        // Verified via: `javap -p Bridge.class`
        private const val ORACLE_INIT_METHOD = "f_SessionValue_oracleInit"
        private const val STEP_SET_VALUE_METHOD = "f_SessionValue_oracleStepSetValue"
        private const val STEP_SET_UPSTREAM_METHOD = "f_SessionValue_oracleStepSetUpstream"
        private const val MAKE_SNAPSHOT_METHOD = "f_SessionValue_oracleMakeSnapshot"
    }
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
