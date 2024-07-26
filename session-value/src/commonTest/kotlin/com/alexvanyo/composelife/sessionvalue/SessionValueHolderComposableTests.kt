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

import androidx.compose.runtime.BroadcastFrameClock
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateListOf
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import app.cash.molecule.RecompositionMode
import app.cash.molecule.moleculeFlow
import app.cash.turbine.test
import com.benasher44.uuid.uuid4
import kotlinx.coroutines.flow.distinctUntilChanged
import kotlinx.coroutines.test.runTest
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertNotEquals
import kotlin.test.assertTrue
import kotlin.collections.removeFirst as removeFirstKt

@Suppress("LargeClass")
class SessionValueHolderComposableTests {

    val broadcastFrameClock = BroadcastFrameClock()

    @Test
    fun whenCreated_stateIsCorrect() = runTest(broadcastFrameClock) {
        val sessionId1 = uuid4()
        val valueId1 = uuid4()

        val pendingUpstreamSessionValues = mutableStateListOf<Pair<SessionValue<Float>, SessionValue<Float>>>()

        val upstreamSessionValue by mutableStateOf(SessionValue(sessionId1, valueId1, 0f))

        moleculeFlow(RecompositionMode.ContextClock) {
            rememberSessionValueHolder(
                upstreamSessionValue = upstreamSessionValue,
                setUpstreamSessionValue = { expected, newValue ->
                    pendingUpstreamSessionValues.add(expected to newValue)
                },
            )
        }
            .distinctUntilChanged()
            .test {
                val sessionValueHolder = awaitItem()

                assertEquals(
                    sessionValueHolder.sessionValue,
                    SessionValue(
                        sessionId1,
                        valueId1,
                        0f,
                    ),
                )
                val info1 = sessionValueHolder.info
                assertFalse(info1.isLocalSessionActive())
                assertEquals(sessionId1, info1.currentUpstreamSessionId)
                assertEquals(sessionId1, info1.preLocalSessionId)
            }
    }

    @Test
    fun whenUpstreamSessionValueUpdated_stateMatches() = runTest(broadcastFrameClock) {
        val sessionId1 = uuid4()
        val valueId1 = uuid4()
        val valueId2 = uuid4()

        val pendingUpstreamSessionValues = mutableStateListOf<Pair<SessionValue<Float>, SessionValue<Float>>>()

        var upstreamSessionValue by mutableStateOf(SessionValue(sessionId1, valueId1, 0f))

        moleculeFlow(RecompositionMode.ContextClock) {
            rememberSessionValueHolder(
                upstreamSessionValue = upstreamSessionValue,
                setUpstreamSessionValue = { upstreamSessionId, sessionValue ->
                    pendingUpstreamSessionValues.add(upstreamSessionId to sessionValue)
                },
            )
        }
            .distinctUntilChanged()
            .test {
                val sessionValueHolder = awaitItem()

                assertEquals(
                    sessionValueHolder.sessionValue,
                    SessionValue(
                        sessionId1,
                        valueId1,
                        0f,
                    ),
                )
                val info1 = sessionValueHolder.info
                assertFalse(info1.isLocalSessionActive())
                val nextLocalSessionId1 = info1.nextLocalSessionId
                assertEquals(nextLocalSessionId1, info1.localSessionId)
                assertEquals(sessionId1, info1.currentUpstreamSessionId)
                assertEquals(sessionId1, info1.preLocalSessionId)

                upstreamSessionValue = SessionValue(sessionId1, valueId2, 1f)
                broadcastFrameClock.sendFrame(1)

                assertEquals(
                    sessionValueHolder.sessionValue,
                    SessionValue(
                        sessionId1,
                        valueId2,
                        1f,
                    ),
                )
                val info2 = sessionValueHolder.info
                assertFalse(info2.isLocalSessionActive())
                val nextLocalSessionId2 = info2.nextLocalSessionId
                assertEquals(nextLocalSessionId2, info2.nextLocalSessionId)
                assertEquals(nextLocalSessionId2, info2.localSessionId)
                assertEquals(sessionId1, info2.currentUpstreamSessionId)
                assertEquals(sessionId1, info2.preLocalSessionId)

                // Updating the upstream session value should cycle the next session id
                assertNotEquals(nextLocalSessionId1, nextLocalSessionId2)
            }
    }

    @Test
    fun whenUpstreamSessionIdUpdated_stateMatches() = runTest(broadcastFrameClock) {
        val sessionId1 = uuid4()
        val sessionId2 = uuid4()
        val valueId1 = uuid4()
        val valueId2 = uuid4()

        val pendingUpstreamSessionValues = mutableStateListOf<Pair<SessionValue<Float>, SessionValue<Float>>>()

        var upstreamSessionValue by mutableStateOf(SessionValue(sessionId1, valueId1, 0f))

        moleculeFlow(RecompositionMode.ContextClock) {
            rememberSessionValueHolder(
                upstreamSessionValue = upstreamSessionValue,
                setUpstreamSessionValue = { upstreamSessionId, sessionValue ->
                    pendingUpstreamSessionValues.add(upstreamSessionId to sessionValue)
                },
            )
        }
            .distinctUntilChanged()
            .test {
                val sessionValueHolder = awaitItem()

                assertEquals(
                    sessionValueHolder.sessionValue,
                    SessionValue(
                        sessionId1,
                        valueId1,
                        0f,
                    ),
                )
                val info1 = sessionValueHolder.info
                assertFalse(info1.isLocalSessionActive())
                val nextLocalSessionId1 = info1.nextLocalSessionId
                assertEquals(nextLocalSessionId1, info1.localSessionId)
                assertEquals(sessionId1, info1.currentUpstreamSessionId)
                assertEquals(sessionId1, info1.preLocalSessionId)

                upstreamSessionValue = SessionValue(sessionId2, valueId2, 1f)
                broadcastFrameClock.sendFrame(1)

                assertEquals(
                    sessionValueHolder.sessionValue,
                    SessionValue(
                        sessionId2,
                        valueId2,
                        1f,
                    ),
                )
                val info2 = sessionValueHolder.info
                assertFalse(info2.isLocalSessionActive())
                val nextLocalSessionId2 = info2.nextLocalSessionId
                assertEquals(nextLocalSessionId2, info2.nextLocalSessionId)
                assertEquals(nextLocalSessionId2, info2.localSessionId)
                assertEquals(sessionId2, info2.currentUpstreamSessionId)
                assertEquals(sessionId2, info2.preLocalSessionId)

                // Updating the upstream session value should cycle the next session id
                assertNotEquals(nextLocalSessionId1, nextLocalSessionId2)
            }
    }

    @Test
    fun whenCreatingLocalSession_stateIsCorrect() = runTest(broadcastFrameClock) {
        val sessionId1 = uuid4()
        val valueId1 = uuid4()
        val valueId2 = uuid4()

        val pendingUpstreamSessionValues = mutableStateListOf<Pair<SessionValue<Float>, SessionValue<Float>>>()

        val upstreamSessionValue by mutableStateOf(SessionValue(sessionId1, valueId1, 0f))

        moleculeFlow(RecompositionMode.ContextClock) {
            rememberSessionValueHolder(
                upstreamSessionValue = upstreamSessionValue,
                setUpstreamSessionValue = { upstreamSessionId, sessionValue ->
                    pendingUpstreamSessionValues.add(upstreamSessionId to sessionValue)
                },
            )
        }
            .distinctUntilChanged()
            .test {
                val sessionValueHolder = awaitItem()

                assertEquals(
                    sessionValueHolder.sessionValue,
                    SessionValue(
                        sessionId1,
                        valueId1,
                        0f,
                    ),
                )
                val info1 = sessionValueHolder.info
                assertFalse(info1.isLocalSessionActive())
                val nextLocalSessionId1 = info1.nextLocalSessionId
                assertEquals(nextLocalSessionId1, info1.localSessionId)
                assertEquals(sessionId1, info1.currentUpstreamSessionId)
                assertEquals(sessionId1, info1.preLocalSessionId)

                sessionValueHolder.setValue(1f, valueId2)
                broadcastFrameClock.sendFrame(1)

                assertEquals(
                    sessionValueHolder.sessionValue,
                    SessionValue(
                        nextLocalSessionId1,
                        valueId2,
                        1f,
                    ),
                )
                val info2 = sessionValueHolder.info
                assertTrue(info2.isLocalSessionActive())
                assertEquals(nextLocalSessionId1, info2.currentLocalSessionId)
                assertEquals(nextLocalSessionId1, info2.localSessionId)
                assertEquals(sessionId1, info2.previousUpstreamSessionId)
                assertEquals(sessionId1, info2.preLocalSessionId)
                assertFalse(info2.isUpstreamSessionValueUpToDate)
                assertEquals(
                    listOf(
                        SessionValue(sessionId1, valueId1, 0f) to SessionValue(nextLocalSessionId1, valueId2, 1f),
                    ),
                    pendingUpstreamSessionValues,
                )
            }
    }

    @Test
    fun localSessionActive_whenUpdatingValue_stateIsCorrect() = runTest(broadcastFrameClock) {
        val sessionId1 = uuid4()
        val valueId1 = uuid4()
        val valueId2 = uuid4()
        val valueId3 = uuid4()

        val pendingUpstreamSessionValues = mutableStateListOf<Pair<SessionValue<Float>, SessionValue<Float>>>()

        val upstreamSessionValue by mutableStateOf(SessionValue(sessionId1, valueId1, 0f))

        moleculeFlow(RecompositionMode.ContextClock) {
            rememberSessionValueHolder(
                upstreamSessionValue = upstreamSessionValue,
                setUpstreamSessionValue = { upstreamSessionId, sessionValue ->
                    pendingUpstreamSessionValues.add(upstreamSessionId to sessionValue)
                },
            )
        }
            .distinctUntilChanged()
            .test {
                val sessionValueHolder = awaitItem()

                assertEquals(
                    sessionValueHolder.sessionValue,
                    SessionValue(
                        sessionId1,
                        valueId1,
                        0f,
                    ),
                )
                val info1 = sessionValueHolder.info
                assertFalse(info1.isLocalSessionActive())
                val nextLocalSessionId1 = info1.nextLocalSessionId
                assertEquals(nextLocalSessionId1, info1.localSessionId)
                assertEquals(sessionId1, info1.currentUpstreamSessionId)
                assertEquals(sessionId1, info1.preLocalSessionId)

                sessionValueHolder.setValue(1f, valueId2)
                broadcastFrameClock.sendFrame(1)

                assertEquals(
                    sessionValueHolder.sessionValue,
                    SessionValue(
                        nextLocalSessionId1,
                        valueId2,
                        1f,
                    ),
                )
                val info2 = sessionValueHolder.info
                assertTrue(info2.isLocalSessionActive())
                assertEquals(nextLocalSessionId1, info2.currentLocalSessionId)
                assertEquals(nextLocalSessionId1, info2.localSessionId)
                assertEquals(sessionId1, info2.previousUpstreamSessionId)
                assertEquals(sessionId1, info2.preLocalSessionId)

                sessionValueHolder.setValue(2f, valueId3)
                broadcastFrameClock.sendFrame(2)

                assertEquals(
                    sessionValueHolder.sessionValue,
                    SessionValue(
                        nextLocalSessionId1,
                        valueId3,
                        2f,
                    ),
                )
                val info3 = sessionValueHolder.info
                assertTrue(info3.isLocalSessionActive())
                assertEquals(nextLocalSessionId1, info3.currentLocalSessionId)
                assertEquals(nextLocalSessionId1, info3.localSessionId)
                assertEquals(sessionId1, info3.previousUpstreamSessionId)
                assertEquals(sessionId1, info3.preLocalSessionId)
                assertFalse(info2.isUpstreamSessionValueUpToDate)
                assertEquals(
                    listOf(
                        SessionValue(sessionId1, valueId1, 0f) to
                            SessionValue(nextLocalSessionId1, valueId2, 1f),
                        SessionValue(nextLocalSessionId1, valueId2, 1f) to
                            SessionValue(nextLocalSessionId1, valueId3, 2f),
                    ),
                    pendingUpstreamSessionValues,
                )
            }
    }

    @Test
    fun localSessionActive_whenUpstreamSessionCatchesUp_stateIsCorrect() = runTest(broadcastFrameClock) {
        val sessionId1 = uuid4()
        val valueId1 = uuid4()
        val valueId2 = uuid4()

        val pendingUpstreamSessionValues = mutableStateListOf<Pair<SessionValue<Float>, SessionValue<Float>>>()

        var upstreamSessionValue by mutableStateOf(SessionValue(sessionId1, valueId1, 0f))

        moleculeFlow(RecompositionMode.ContextClock) {
            rememberSessionValueHolder(
                upstreamSessionValue = upstreamSessionValue,
                setUpstreamSessionValue = { upstreamSessionId, sessionValue ->
                    pendingUpstreamSessionValues.add(upstreamSessionId to sessionValue)
                },
            )
        }
            .distinctUntilChanged()
            .test {
                val sessionValueHolder = awaitItem()

                assertEquals(
                    sessionValueHolder.sessionValue,
                    SessionValue(
                        sessionId1,
                        valueId1,
                        0f,
                    ),
                )
                val info1 = sessionValueHolder.info
                assertFalse(info1.isLocalSessionActive())
                val nextLocalSessionId1 = info1.nextLocalSessionId
                assertEquals(nextLocalSessionId1, info1.localSessionId)
                assertEquals(sessionId1, info1.currentUpstreamSessionId)
                assertEquals(sessionId1, info1.preLocalSessionId)

                sessionValueHolder.setValue(1f, valueId2)
                broadcastFrameClock.sendFrame(1)

                assertEquals(
                    sessionValueHolder.sessionValue,
                    SessionValue(
                        nextLocalSessionId1,
                        valueId2,
                        1f,
                    ),
                )
                val info2 = sessionValueHolder.info
                assertTrue(info2.isLocalSessionActive())
                assertEquals(nextLocalSessionId1, info2.currentLocalSessionId)
                assertEquals(nextLocalSessionId1, info2.localSessionId)
                assertEquals(sessionId1, info2.previousUpstreamSessionId)
                assertEquals(sessionId1, info2.preLocalSessionId)
                assertFalse(info2.isUpstreamSessionValueUpToDate)
                assertEquals(
                    listOf(
                        SessionValue(sessionId1, valueId1, 0f) to SessionValue(nextLocalSessionId1, valueId2, 1f),
                    ),
                    pendingUpstreamSessionValues,
                )

                upstreamSessionValue = pendingUpstreamSessionValues.removeFirstKt().second
                broadcastFrameClock.sendFrame(2)

                assertEquals(
                    sessionValueHolder.sessionValue,
                    SessionValue(
                        nextLocalSessionId1,
                        valueId2,
                        1f,
                    ),
                )
                val info3 = sessionValueHolder.info
                assertTrue(info3.isLocalSessionActive())
                assertEquals(nextLocalSessionId1, info3.currentLocalSessionId)
                assertEquals(nextLocalSessionId1, info3.localSessionId)
                assertEquals(sessionId1, info3.previousUpstreamSessionId)
                assertEquals(sessionId1, info3.preLocalSessionId)
                assertTrue(info3.isUpstreamSessionValueUpToDate)
                assertEquals(
                    emptyList(),
                    pendingUpstreamSessionValues,
                )
            }
    }

    @Test
    fun localSessionActive_whenUpstreamSessionCatchesUpWithTwoChanges_stateIsCorrect() = runTest(broadcastFrameClock) {
        val sessionId1 = uuid4()
        val valueId1 = uuid4()
        val valueId2 = uuid4()
        val valueId3 = uuid4()

        val pendingUpstreamSessionValues = mutableStateListOf<Pair<SessionValue<Float>, SessionValue<Float>>>()

        var upstreamSessionValue by mutableStateOf(SessionValue(sessionId1, valueId1, 0f))

        moleculeFlow(RecompositionMode.ContextClock) {
            rememberSessionValueHolder(
                upstreamSessionValue = upstreamSessionValue,
                setUpstreamSessionValue = { upstreamSessionId, sessionValue ->
                    pendingUpstreamSessionValues.add(upstreamSessionId to sessionValue)
                },
            )
        }
            .distinctUntilChanged()
            .test {
                val sessionValueHolder = awaitItem()

                assertEquals(
                    sessionValueHolder.sessionValue,
                    SessionValue(
                        sessionId1,
                        valueId1,
                        0f,
                    ),
                )
                val info1 = sessionValueHolder.info
                assertFalse(info1.isLocalSessionActive())
                val nextLocalSessionId1 = info1.nextLocalSessionId
                assertEquals(nextLocalSessionId1, info1.localSessionId)
                assertEquals(sessionId1, info1.currentUpstreamSessionId)
                assertEquals(sessionId1, info1.preLocalSessionId)

                sessionValueHolder.setValue(1f, valueId2)
                broadcastFrameClock.sendFrame(1)

                assertEquals(
                    sessionValueHolder.sessionValue,
                    SessionValue(
                        nextLocalSessionId1,
                        valueId2,
                        1f,
                    ),
                )
                val info2 = sessionValueHolder.info
                assertTrue(info2.isLocalSessionActive())
                assertEquals(nextLocalSessionId1, info2.currentLocalSessionId)
                assertEquals(nextLocalSessionId1, info2.localSessionId)
                assertEquals(sessionId1, info2.previousUpstreamSessionId)
                assertEquals(sessionId1, info2.preLocalSessionId)
                assertFalse(info2.isUpstreamSessionValueUpToDate)
                assertEquals(
                    listOf(
                        SessionValue(sessionId1, valueId1, 0f) to SessionValue(nextLocalSessionId1, valueId2, 1f),
                    ),
                    pendingUpstreamSessionValues,
                )

                sessionValueHolder.setValue(2f, valueId3)
                broadcastFrameClock.sendFrame(2)

                assertEquals(
                    sessionValueHolder.sessionValue,
                    SessionValue(
                        nextLocalSessionId1,
                        valueId3,
                        2f,
                    ),
                )
                val info3 = sessionValueHolder.info
                assertTrue(info3.isLocalSessionActive())
                assertEquals(nextLocalSessionId1, info3.currentLocalSessionId)
                assertEquals(nextLocalSessionId1, info3.localSessionId)
                assertEquals(sessionId1, info3.previousUpstreamSessionId)
                assertEquals(sessionId1, info3.preLocalSessionId)
                assertFalse(info3.isUpstreamSessionValueUpToDate)
                assertEquals(
                    listOf(
                        SessionValue(sessionId1, valueId1, 0f) to SessionValue(nextLocalSessionId1, valueId2, 1f),
                        SessionValue(nextLocalSessionId1, valueId2, 1f) to SessionValue(
                            nextLocalSessionId1,
                            valueId3,
                            2f,
                        ),
                    ),
                    pendingUpstreamSessionValues,
                )

                upstreamSessionValue = pendingUpstreamSessionValues.removeFirstKt().second
                broadcastFrameClock.sendFrame(3)

                assertEquals(
                    sessionValueHolder.sessionValue,
                    SessionValue(
                        nextLocalSessionId1,
                        valueId3,
                        2f,
                    ),
                )
                val info4 = sessionValueHolder.info
                assertTrue(info4.isLocalSessionActive())
                assertEquals(nextLocalSessionId1, info4.currentLocalSessionId)
                assertEquals(nextLocalSessionId1, info4.localSessionId)
                assertEquals(sessionId1, info4.previousUpstreamSessionId)
                assertEquals(sessionId1, info4.preLocalSessionId)
                assertFalse(info4.isUpstreamSessionValueUpToDate)
                assertEquals(
                    listOf(
                        SessionValue(nextLocalSessionId1, valueId2, 1f) to SessionValue(
                            nextLocalSessionId1,
                            valueId3,
                            2f,
                        ),
                    ),
                    pendingUpstreamSessionValues,
                )

                upstreamSessionValue = pendingUpstreamSessionValues.removeFirstKt().second
                broadcastFrameClock.sendFrame(4)

                assertEquals(
                    sessionValueHolder.sessionValue,
                    SessionValue(
                        nextLocalSessionId1,
                        valueId3,
                        2f,
                    ),
                )
                val info5 = sessionValueHolder.info
                assertTrue(info5.isLocalSessionActive())
                assertEquals(nextLocalSessionId1, info5.currentLocalSessionId)
                assertEquals(nextLocalSessionId1, info5.localSessionId)
                assertEquals(sessionId1, info5.previousUpstreamSessionId)
                assertEquals(sessionId1, info5.preLocalSessionId)
                assertTrue(info5.isUpstreamSessionValueUpToDate)
                assertEquals(
                    emptyList(),
                    pendingUpstreamSessionValues,
                )
            }
    }

    @Test
    fun localSessionActive_whenUpstreamSessionChanges_stateIsCorrect() = runTest(broadcastFrameClock) {
        val sessionId1 = uuid4()
        val sessionId2 = uuid4()
        val valueId1 = uuid4()
        val valueId2 = uuid4()
        val valueId3 = uuid4()

        val pendingUpstreamSessionValues = mutableStateListOf<Pair<SessionValue<Float>, SessionValue<Float>>>()

        var upstreamSessionValue by mutableStateOf(SessionValue(sessionId1, valueId1, 0f))

        moleculeFlow(RecompositionMode.ContextClock) {
            rememberSessionValueHolder(
                upstreamSessionValue = upstreamSessionValue,
                setUpstreamSessionValue = { upstreamSessionId, sessionValue ->
                    pendingUpstreamSessionValues.add(upstreamSessionId to sessionValue)
                },
            )
        }
            .distinctUntilChanged()
            .test {
                val sessionValueHolder = awaitItem()

                assertEquals(
                    sessionValueHolder.sessionValue,
                    SessionValue(
                        sessionId1,
                        valueId1,
                        0f,
                    ),
                )
                val info1 = sessionValueHolder.info
                assertFalse(info1.isLocalSessionActive())
                val nextLocalSessionId1 = info1.nextLocalSessionId
                assertEquals(nextLocalSessionId1, info1.localSessionId)
                assertEquals(sessionId1, info1.currentUpstreamSessionId)
                assertEquals(sessionId1, info1.preLocalSessionId)

                sessionValueHolder.setValue(1f, valueId2)
                broadcastFrameClock.sendFrame(1)

                assertEquals(
                    sessionValueHolder.sessionValue,
                    SessionValue(
                        nextLocalSessionId1,
                        valueId2,
                        1f,
                    ),
                )
                val info2 = sessionValueHolder.info
                assertTrue(info2.isLocalSessionActive())
                assertEquals(nextLocalSessionId1, info2.currentLocalSessionId)
                assertEquals(nextLocalSessionId1, info2.localSessionId)
                assertEquals(sessionId1, info2.previousUpstreamSessionId)
                assertEquals(sessionId1, info2.preLocalSessionId)
                assertFalse(info2.isUpstreamSessionValueUpToDate)
                assertEquals(
                    listOf(
                        SessionValue(sessionId1, valueId1, 0f) to SessionValue(nextLocalSessionId1, valueId2, 1f),
                    ),
                    pendingUpstreamSessionValues,
                )

                upstreamSessionValue = SessionValue(
                    sessionId2,
                    valueId3,
                    1f,
                )
                broadcastFrameClock.sendFrame(2)

                assertEquals(
                    sessionValueHolder.sessionValue,
                    SessionValue(
                        sessionId2,
                        valueId3,
                        1f,
                    ),
                )
                val info3 = sessionValueHolder.info
                assertFalse(info3.isLocalSessionActive())
                val nextLocalSessionId2 = info3.nextLocalSessionId
                assertEquals(nextLocalSessionId2, info3.localSessionId)
                assertEquals(sessionId2, info3.currentUpstreamSessionId)
                assertEquals(sessionId2, info3.preLocalSessionId)

                // Updating the upstream session value should cycle the next session id
                assertNotEquals(nextLocalSessionId1, nextLocalSessionId2)
            }
    }

    @Test
    fun localSessionActive_whenUpstreamSessionChangesBeforeLocalSession_stateIsCorrect() = runTest(
        broadcastFrameClock,
    ) {
        val sessionId1 = uuid4()
        val valueId1 = uuid4()
        val valueId2 = uuid4()
        val valueId3 = uuid4()

        val pendingUpstreamSessionValues = mutableStateListOf<Pair<SessionValue<Float>, SessionValue<Float>>>()

        var upstreamSessionValue by mutableStateOf(SessionValue(sessionId1, valueId1, 0f))

        moleculeFlow(RecompositionMode.ContextClock) {
            rememberSessionValueHolder(
                upstreamSessionValue = upstreamSessionValue,
                setUpstreamSessionValue = { upstreamSessionId, sessionValue ->
                    pendingUpstreamSessionValues.add(upstreamSessionId to sessionValue)
                },
            )
        }
            .distinctUntilChanged()
            .test {
                val sessionValueHolder = awaitItem()

                assertEquals(
                    sessionValueHolder.sessionValue,
                    SessionValue(
                        sessionId1,
                        valueId1,
                        0f,
                    ),
                )
                val info1 = sessionValueHolder.info
                assertFalse(info1.isLocalSessionActive())
                val nextLocalSessionId1 = info1.nextLocalSessionId
                assertEquals(nextLocalSessionId1, info1.localSessionId)
                assertEquals(sessionId1, info1.currentUpstreamSessionId)
                assertEquals(sessionId1, info1.preLocalSessionId)

                sessionValueHolder.setValue(1f, valueId2)
                broadcastFrameClock.sendFrame(1)

                assertEquals(
                    sessionValueHolder.sessionValue,
                    SessionValue(
                        nextLocalSessionId1,
                        valueId2,
                        1f,
                    ),
                )
                val info2 = sessionValueHolder.info
                assertTrue(info2.isLocalSessionActive())
                assertEquals(nextLocalSessionId1, info2.currentLocalSessionId)
                assertEquals(nextLocalSessionId1, info2.localSessionId)
                assertEquals(sessionId1, info2.previousUpstreamSessionId)
                assertEquals(sessionId1, info2.preLocalSessionId)
                assertFalse(info2.isUpstreamSessionValueUpToDate)
                assertEquals(
                    listOf(
                        SessionValue(sessionId1, valueId1, 0f) to SessionValue(nextLocalSessionId1, valueId2, 1f),
                    ),
                    pendingUpstreamSessionValues,
                )

                upstreamSessionValue = SessionValue(
                    sessionId1,
                    valueId3,
                    2f,
                )
                broadcastFrameClock.sendFrame(2)

                assertEquals(
                    sessionValueHolder.sessionValue,
                    SessionValue(
                        sessionId1,
                        valueId3,
                        2f,
                    ),
                )
                val info3 = sessionValueHolder.info
                assertFalse(info3.isLocalSessionActive())
                val nextLocalSessionId2 = info3.nextLocalSessionId
                assertEquals(nextLocalSessionId2, info3.localSessionId)
                assertEquals(sessionId1, info3.currentUpstreamSessionId)
                assertEquals(sessionId1, info3.preLocalSessionId)

                // Updating the upstream session value should cycle the next session id
                assertNotEquals(nextLocalSessionId1, nextLocalSessionId2)
            }
    }
}
