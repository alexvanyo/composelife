/*
 * Copyright 2024 The Android Open Source Project
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

import kotlinx.serialization.Serializable
import kotlinx.serialization.json.Json
import java.io.BufferedReader
import java.io.BufferedWriter
import java.io.File
import java.io.InputStreamReader
import java.io.OutputStreamWriter
import kotlin.test.AfterTest
import kotlin.test.BeforeTest
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
import kotlin.uuid.ExperimentalUuidApi
import kotlin.uuid.Uuid

@OptIn(ExperimentalUuidApi::class)
private fun Long.toUuid(): Uuid = Uuid.fromLongs(0L, this)

@OptIn(ExperimentalUuidApi::class)
private fun Uuid.toLeanId(): Long = this.toLongs { _, lsb -> lsb }

/**
 * Conformance test suite verifying that production Kotlin [SessionValueState] faithfully
 * matches the Lean 4 formal specification and executable oracle at every transition step.
 */
@OptIn(ExperimentalUuidApi::class)
class SessionValueLeanConformanceTests {

    private lateinit var oracleProcess: Process
    private lateinit var reader: BufferedReader
    private lateinit var writer: BufferedWriter

    private val json = Json { ignoreUnknownKeys = true }

    private sealed interface OracleCommand {
        fun toCommandLine(): String

        data class Init(val upstream: SessionValue<String>, val localSessionId: Uuid) : OracleCommand {
            override fun toCommandLine(): String =
                "INIT ${upstream.sessionId.toLeanId()} ${upstream.valueId.toLeanId()} ${upstream.value} " +
                    "${localSessionId.toLeanId()}"
        }

        data class SetValue(val value: String, val valueId: Uuid) : OracleCommand {
            override fun toCommandLine(): String = "SET_VALUE $value ${valueId.toLeanId()}"
        }

        data class SetUpstream(val upstream: SessionValue<String>, val freshLocalSessionId: Uuid) : OracleCommand {
            override fun toCommandLine(): String =
                "SET_UPSTREAM ${upstream.sessionId.toLeanId()} ${upstream.valueId.toLeanId()} ${upstream.value} " +
                    "${freshLocalSessionId.toLeanId()}"
        }

        data object Exit : OracleCommand {
            override fun toCommandLine(): String = "EXIT"
        }
    }

    @Serializable
    private data class LeanSnapshot(
        val exposedSessionId: Long,
        val exposedValueId: Long,
        val exposedValue: String,
        val isLocalSessionActive: Boolean,
        val localSessionId: Long,
        val preLocalSessionId: Long,
        val isUpstreamUpToDate: Boolean,
        val lastExpectedSessionId: Long,
        val lastExpectedValueId: Long,
    )

    @BeforeTest
    fun setUp() {
        val oracleBinary = File("lean/.lake/build/bin/SessionValueOracle")
        check(oracleBinary.exists() && oracleBinary.canExecute()) {
            "SessionValueOracle executable not found at ${oracleBinary.absolutePath}! " +
                "Run 'lake build SessionValueOracle' in session-value/lean."
        }

        oracleProcess = ProcessBuilder(oracleBinary.absolutePath).start()
        reader = BufferedReader(InputStreamReader(oracleProcess.inputStream))
        writer = BufferedWriter(OutputStreamWriter(oracleProcess.outputStream))
    }

    @AfterTest
    fun tearDown() {
        try {
            writer.write("${OracleCommand.Exit.toCommandLine()}\n")
            writer.flush()
        } catch (_: Exception) {
            // Process may have already exited
        }
        oracleProcess.destroy()
    }

    private fun sendCommand(command: OracleCommand): LeanSnapshot {
        writer.write("${command.toCommandLine()}\n")
        writer.flush()
        val line = reader.readLine()
        assertNotNull(line, "Oracle process terminated unexpectedly")
        return json.decodeFromString<LeanSnapshot>(line)
    }

    private fun assertMatchesLean(kotlinState: SessionValueState<String>, lean: LeanSnapshot, message: String = "") {
        assertEquals(
            lean.exposedSessionId,
            kotlinState.sessionValue.sessionId.toLeanId(),
            "$message: exposedSessionId mismatch",
        )
        assertEquals(
            lean.exposedValueId,
            kotlinState.sessionValue.valueId.toLeanId(),
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
            kotlinState.info.localSessionId.toLeanId(),
            "$message: localSessionId mismatch",
        )
        assertEquals(
            lean.preLocalSessionId,
            kotlinState.info.preLocalSessionId.toLeanId(),
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

        val lean = sendCommand(OracleCommand.Init(u0, localId))
        assertMatchesLean(kotlinState, lean, "Initial State")
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
        var lean = sendCommand(OracleCommand.Init(u0, localId))
        assertMatchesLean(kotlinState, lean)

        // First local update
        val (kState1, _) = kotlinState.stepSetValue("Update1", 40L.toUuid())
        kotlinState = kState1
        lean = sendCommand(OracleCommand.SetValue("Update1", 40L.toUuid()))
        assertMatchesLean(kotlinState, lean, "First local update")

        // Second local update
        val (kState2, _) = kotlinState.stepSetValue("Update2", 41L.toUuid())
        kotlinState = kState2
        lean = sendCommand(OracleCommand.SetValue("Update2", 41L.toUuid()))
        assertMatchesLean(kotlinState, lean, "Second local update")
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
        sendCommand(OracleCommand.Init(u0, localId))

        // Set local value to 30L:40L:"Val1"
        val (kState1, _) = kotlinState.stepSetValue("Val1", 40L.toUuid())
        kotlinState = kState1
        sendCommand(OracleCommand.SetValue("Val1", 40L.toUuid()))

        // Set another local value to 30L:41L:"Val2"
        val (kState2, _) = kotlinState.stepSetValue("Val2", 41L.toUuid())
        kotlinState = kState2
        sendCommand(OracleCommand.SetValue("Val2", 41L.toUuid()))

        // Echo of first local value arrives (valueId 40L) -> should be active, but not up to date
        val echo1 = SessionValue(localId, 40L.toUuid(), "Val1")
        kotlinState = kotlinState.stepSetValueFromUpstream(echo1, 99L.toUuid())
        var lean = sendCommand(OracleCommand.SetUpstream(echo1, 99L.toUuid()))
        assertMatchesLean(kotlinState, lean, "Partial echo")
        assertEquals(false, lean.isUpstreamUpToDate)

        // Echo of latest local value arrives (valueId 41L) -> should be active and up to date!
        val echo2 = SessionValue(localId, 41L.toUuid(), "Val2")
        kotlinState = kotlinState.stepSetValueFromUpstream(echo2, 99L.toUuid())
        lean = sendCommand(OracleCommand.SetUpstream(echo2, 99L.toUuid()))
        assertMatchesLean(kotlinState, lean, "Complete echo")
        assertEquals(true, lean.isUpstreamUpToDate)
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
        sendCommand(OracleCommand.Init(u0, localId))

        // Make a local edit
        val (kState1, _) = kotlinState.stepSetValue("LocalDraft", 40L.toUuid())
        kotlinState = kState1
        sendCommand(OracleCommand.SetValue("LocalDraft", 40L.toUuid()))

        // A foreign session 99L commits upstream
        val foreignUpstream = SessionValue(99L.toUuid(), 100L.toUuid(), "ForeignData")
        kotlinState = kotlinState.stepSetValueFromUpstream(foreignUpstream, 50L.toUuid())
        val lean = sendCommand(OracleCommand.SetUpstream(foreignUpstream, 50L.toUuid()))

        assertMatchesLean(kotlinState, lean, "Foreign conflict invalidation")
        assertEquals(false, kotlinState.info.isLocalSessionActive())
        assertEquals("ForeignData", kotlinState.sessionValue.value)
        assertEquals(99L.toUuid(), kotlinState.sessionValue.sessionId)
        assertEquals(50L.toUuid(), kotlinState.info.localSessionId)
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
        sendCommand(OracleCommand.Init(u0, localId))

        // Upstream changes while inactive
        val nextUpstream = SessionValue(11L.toUuid(), 21L.toUuid(), "Changed")
        kotlinState = kotlinState.stepSetValueFromUpstream(nextUpstream, 31L.toUuid())
        val lean = sendCommand(OracleCommand.SetUpstream(nextUpstream, 31L.toUuid()))

        assertMatchesLean(kotlinState, lean, "Inactive upstream change")
        assertEquals(false, kotlinState.info.isLocalSessionActive())
        assertEquals(31L.toUuid(), kotlinState.info.localSessionId)
        assertEquals(11L.toUuid(), kotlinState.info.preLocalSessionId)
    }

    @Test
    fun fuzzedRandomizedActionTrace_matchesLean() {
        val u0 = SessionValue(1L.toUuid(), 1L.toUuid(), "v0")
        val localId = 100L.toUuid()
        var kotlinState = SessionValueState(
            upstreamSessionIdBeforeLocalSession = u0.sessionId,
            upstreamSessionValue = u0,
            localSessionId = localId,
            localSessionValue = null,
        )
        var lean = sendCommand(OracleCommand.Init(u0, localId))
        assertMatchesLean(kotlinState, lean, "Fuzz start")

        val rng = kotlin.random.Random(12345)
        var nextId = 200L

        for (step in 1..100) {
            when (rng.nextInt(3)) {
                0 -> {
                    // Local edit
                    val valId = nextId++.toUuid()
                    val newVal = "val_$valId"
                    val (kState, _) = kotlinState.stepSetValue(newVal, valId)
                    kotlinState = kState
                    lean = sendCommand(OracleCommand.SetValue(newVal, valId))
                }

                1 -> {
                    // Upstream echo (same session as local or old upstream)
                    val activeSession = kotlinState.info.localSessionId
                    val valId = nextId++.toUuid()
                    val newVal = "echo_$valId"
                    val freshId = nextId++.toUuid()
                    val newUpstream = SessionValue(activeSession, valId, newVal)
                    kotlinState = kotlinState.stepSetValueFromUpstream(newUpstream, freshId)
                    lean = sendCommand(OracleCommand.SetUpstream(newUpstream, freshId))
                }

                2 -> {
                    // Foreign upstream update
                    val foreignSess = nextId++.toUuid()
                    val valId = nextId++.toUuid()
                    val newVal = "foreign_$valId"
                    val freshId = nextId++.toUuid()
                    val newUpstream = SessionValue(foreignSess, valId, newVal)
                    kotlinState = kotlinState.stepSetValueFromUpstream(newUpstream, freshId)
                    lean = sendCommand(OracleCommand.SetUpstream(newUpstream, freshId))
                }
            }
            assertMatchesLean(kotlinState, lean, "Fuzz step $step")
        }
    }
}
