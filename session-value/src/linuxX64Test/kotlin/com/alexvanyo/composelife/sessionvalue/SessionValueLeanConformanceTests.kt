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

package com.alexvanyo.composelife.sessionvalue

import com.alexvanyo.composelife.sessionvalue.lean.LeanSessionValueOracle
import com.alexvanyo.composelife.sessionvalue.lean.LeanSnapshot
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.uuid.ExperimentalUuidApi
import kotlin.uuid.Uuid

@OptIn(ExperimentalUuidApi::class)
private fun Long.toUuid(highBits: Long = 0x123456789abcdef0L): Uuid = Uuid.fromLongs(highBits, this)

/**
 * Conformance test suite verifying that production Kotlin [SessionValueState] faithfully
 * matches the Lean 4 formal specification and executable oracle via JNI at every transition step.
 */
@OptIn(ExperimentalUuidApi::class)
class SessionValueLeanConformanceTests {

    private fun createOracle(upstream: SessionValue<String>, localSessionId: Uuid): LeanSessionValueOracle =
        LeanSessionValueOracle(
            upstreamSessionId = upstream.sessionId,
            upstreamValueId = upstream.valueId,
            upstreamValue = upstream.value,
            localSessionId = localSessionId,
        )

    private fun LeanSessionValueOracle.stepSetUpstream(
        upstream: SessionValue<String>,
        freshLocalSessionId: Uuid,
    ): LeanSnapshot = stepSetUpstream(
        upstreamSessionId = upstream.sessionId,
        upstreamValueId = upstream.valueId,
        upstreamValue = upstream.value,
        freshLocalSessionId = freshLocalSessionId,
    )

    private fun assertMatchesLean(kotlinState: SessionValueState<String>, lean: LeanSnapshot, message: String = "") {
        assertEquals(
            lean.exposedSessionId,
            kotlinState.sessionValue.sessionId,
            "$message: exposedSessionId mismatch",
        )
        assertEquals(
            lean.exposedValueId,
            kotlinState.sessionValue.valueId,
            "$message: exposedValueId mismatch",
        )
        assertEquals(
            lean.exposedValue,
            kotlinState.sessionValue.value,
            "$message: exposedValue mismatch",
        )
        assertEquals(
            lean.isLocalSessionActive,
            kotlinState.info.isLocalSessionActive(),
            "$message: isLocalSessionActive mismatch",
        )
        assertEquals(
            lean.localSessionId,
            kotlinState.info.localSessionId,
            "$message: localSessionId mismatch",
        )
        assertEquals(
            lean.preLocalSessionId,
            kotlinState.info.preLocalSessionId,
            "$message: preLocalSessionId mismatch",
        )
        if (kotlinState.info is LocalSessionInfo.Active) {
            assertEquals(
                lean.isUpstreamUpToDate,
                (kotlinState.info as LocalSessionInfo.Active).isUpstreamSessionValueUpToDate,
                "$message: isUpstreamUpToDate mismatch",
            )
        }
    }

    @Test
    fun initialInactiveState_matchesLean() {
        val u0 = SessionValue(10L.toUuid(), 20L.toUuid(), "Initial")
        val localId = 30L.toUuid()
        val kotlinState = SessionValueState(
            upstreamSessionIdBeforeLocalSession = u0.sessionId,
            upstreamSessionValue = u0,
            localSessionId = localId,
            localSessionValue = null,
        )

        createOracle(u0, localId).use { oracle ->
            val lean = oracle.getSnapshot()
            assertMatchesLean(kotlinState, lean, "Initial State")
        }
    }

    @Test
    fun consecutiveLocalUpdates_matchLean() {
        val u0 = SessionValue(10L.toUuid(), 20L.toUuid(), "Initial")
        val localId = 30L.toUuid()
        var kotlinState = SessionValueState(
            upstreamSessionIdBeforeLocalSession = u0.sessionId,
            upstreamSessionValue = u0,
            localSessionId = localId,
            localSessionValue = null,
        )
        createOracle(u0, localId).use { oracle ->
            var lean = oracle.getSnapshot()
            assertMatchesLean(kotlinState, lean)

            // First local update
            val (kState1, _) = kotlinState.stepSetValue("Update1", 40L.toUuid())
            kotlinState = kState1
            lean = oracle.stepSetValue("Update1", 40L.toUuid())
            assertMatchesLean(kotlinState, lean, "First local update")

            // Second local update
            val (kState2, _) = kotlinState.stepSetValue("Update2", 41L.toUuid())
            kotlinState = kState2
            lean = oracle.stepSetValue("Update2", 41L.toUuid())
            assertMatchesLean(kotlinState, lean, "Second local update")
        }
    }

    @Test
    fun upstreamEcho_keepsSessionActive_andCatchesUp() {
        val u0 = SessionValue(10L.toUuid(), 20L.toUuid(), "Initial")
        val localId = 30L.toUuid()
        var kotlinState = SessionValueState(
            upstreamSessionIdBeforeLocalSession = u0.sessionId,
            upstreamSessionValue = u0,
            localSessionId = localId,
            localSessionValue = null,
        )
        createOracle(u0, localId).use { oracle ->
            // Set local value to 30L:40L:"Val1"
            val (kState1, _) = kotlinState.stepSetValue("Val1", 40L.toUuid())
            kotlinState = kState1
            oracle.stepSetValue("Val1", 40L.toUuid())

            // Set another local value to 30L:41L:"Val2"
            val (kState2, _) = kotlinState.stepSetValue("Val2", 41L.toUuid())
            kotlinState = kState2
            oracle.stepSetValue("Val2", 41L.toUuid())

            // Echo of first local value arrives (valueId 40L) -> should be active, but not up to date
            val echo1 = SessionValue(localId, 40L.toUuid(), "Val1")
            kotlinState = kotlinState.stepSetValueFromUpstream(echo1, 99L.toUuid())
            var lean = oracle.stepSetUpstream(echo1, 99L.toUuid())
            assertMatchesLean(kotlinState, lean, "Partial echo")
            assertEquals(false, lean.isUpstreamUpToDate)

            // Echo of latest local value arrives (valueId 41L) -> should be active and up to date!
            val echo2 = SessionValue(localId, 41L.toUuid(), "Val2")
            kotlinState = kotlinState.stepSetValueFromUpstream(echo2, 99L.toUuid())
            lean = oracle.stepSetUpstream(echo2, 99L.toUuid())
            assertMatchesLean(kotlinState, lean, "Complete echo")
            assertEquals(true, lean.isUpstreamUpToDate)
        }
    }

    @Test
    fun conflictingForeignSession_invalidatesLocalSession_matchesLean() {
        val u0 = SessionValue(10L.toUuid(), 20L.toUuid(), "Initial")
        val localId = 30L.toUuid()
        var kotlinState = SessionValueState(
            upstreamSessionIdBeforeLocalSession = u0.sessionId,
            upstreamSessionValue = u0,
            localSessionId = localId,
            localSessionValue = null,
        )
        createOracle(u0, localId).use { oracle ->
            // Make a local edit
            val (kState1, _) = kotlinState.stepSetValue("LocalDraft", 40L.toUuid())
            kotlinState = kState1
            oracle.stepSetValue("LocalDraft", 40L.toUuid())

            // A foreign session 99L commits upstream
            val foreignUpstream = SessionValue(99L.toUuid(), 100L.toUuid(), "ForeignData")
            kotlinState = kotlinState.stepSetValueFromUpstream(foreignUpstream, 50L.toUuid())
            val lean = oracle.stepSetUpstream(foreignUpstream, 50L.toUuid())

            assertMatchesLean(kotlinState, lean, "Foreign conflict invalidation")
            assertEquals(false, kotlinState.info.isLocalSessionActive())
            assertEquals("ForeignData", kotlinState.sessionValue.value)
            assertEquals(99L.toUuid(), kotlinState.sessionValue.sessionId)
            assertEquals(50L.toUuid(), kotlinState.info.localSessionId)
        }
    }

    @Test
    fun inactiveUpstreamChanges_cycleNextLocalSessionId_matchesLean() {
        val u0 = SessionValue(10L.toUuid(), 20L.toUuid(), "Initial")
        val localId = 30L.toUuid()
        var kotlinState = SessionValueState(
            upstreamSessionIdBeforeLocalSession = u0.sessionId,
            upstreamSessionValue = u0,
            localSessionId = localId,
            localSessionValue = null,
        )
        createOracle(u0, localId).use { oracle ->
            // Upstream changes while inactive
            val nextUpstream = SessionValue(11L.toUuid(), 21L.toUuid(), "Changed")
            kotlinState = kotlinState.stepSetValueFromUpstream(nextUpstream, 31L.toUuid())
            val lean = oracle.stepSetUpstream(nextUpstream, 31L.toUuid())

            assertMatchesLean(kotlinState, lean, "Inactive upstream change")
            assertEquals(false, kotlinState.info.isLocalSessionActive())
            assertEquals(31L.toUuid(), kotlinState.info.localSessionId)
            assertEquals(11L.toUuid(), kotlinState.info.preLocalSessionId)
        }
    }

    @Test
    fun fuzzedRandomizedActionTrace_matchesLean() {
        val rng = kotlin.random.Random(12345)
        fun nextUuid(): Uuid = Uuid.fromLongs(rng.nextLong(), rng.nextLong())

        val u0 = SessionValue(nextUuid(), nextUuid(), "v0")
        val localId = nextUuid()
        var kotlinState = SessionValueState(
            upstreamSessionIdBeforeLocalSession = u0.sessionId,
            upstreamSessionValue = u0,
            localSessionId = localId,
            localSessionValue = null,
        )
        createOracle(u0, localId).use { oracle ->
            var lean = oracle.getSnapshot()
            assertMatchesLean(kotlinState, lean, "Fuzz start")

            for (step in 1..100) {
                when (rng.nextInt(3)) {
                    0 -> {
                        // Local edit
                        val valId = nextUuid()
                        val newVal = "val_$valId"
                        val (kState, _) = kotlinState.stepSetValue(newVal, valId)
                        kotlinState = kState
                        lean = oracle.stepSetValue(newVal, valId)
                    }

                    1 -> {
                        // Upstream echo (same session as local or old upstream)
                        val activeSession = kotlinState.info.localSessionId
                        val valId = nextUuid()
                        val newVal = "echo_$valId"
                        val freshId = nextUuid()
                        val newUpstream = SessionValue(activeSession, valId, newVal)
                        kotlinState = kotlinState.stepSetValueFromUpstream(newUpstream, freshId)
                        lean = oracle.stepSetUpstream(newUpstream, freshId)
                    }

                    2 -> {
                        // Foreign upstream update
                        val foreignSess = nextUuid()
                        val valId = nextUuid()
                        val newVal = "foreign_$valId"
                        val freshId = nextUuid()
                        val newUpstream = SessionValue(foreignSess, valId, newVal)
                        kotlinState = kotlinState.stepSetValueFromUpstream(newUpstream, freshId)
                        lean = oracle.stepSetUpstream(newUpstream, freshId)
                    }
                }
                assertMatchesLean(kotlinState, lean, "Fuzz step $step")
            }
        }
    }
}
