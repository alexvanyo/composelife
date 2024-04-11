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

import androidx.compose.runtime.DisposableEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateListOf
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.runComposeUiTest
import com.alexvanyo.composelife.kmpandroidrunner.KmpAndroidJUnit4
import com.alexvanyo.composelife.kmpstaterestorationtester.KmpStateRestorationTester
import org.junit.runner.RunWith
import java.util.UUID
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertNotEquals
import kotlin.test.assertTrue
import kotlin.test.fail

@Suppress("LargeClass")
@OptIn(ExperimentalTestApi::class)
@RunWith(KmpAndroidJUnit4::class)
class SessionValueHolderComposableTests {

    @Test
    fun whenCreated_stateIsCorrect() = runComposeUiTest {
        val sessionId1 = UUID.randomUUID()
        val valueId1 = UUID.randomUUID()

        val pendingUpstreamSessionValues = mutableStateListOf<Pair<SessionValue<Float>, SessionValue<Float>>>()

        lateinit var sessionValueHolder: SessionValueHolder<Float>
        val upstreamSessionValue by mutableStateOf(SessionValue(sessionId1, valueId1, 0f))

        setContent {
            sessionValueHolder = rememberSessionValueHolder(
                upstreamSessionValue = upstreamSessionValue,
                setUpstreamSessionValue = { expected, newValue ->
                    pendingUpstreamSessionValues.add(expected to newValue)
                },
            )
        }

        assertEquals(
            sessionValueHolder.sessionValue,
            SessionValue(
                sessionId1,
                valueId1,
                0f,
            ),
        )
        assertFalse(sessionValueHolder.info.isLocalSessionActive())
    }

    @Test
    fun whenUpstreamSessionValueUpdated_stateMatches() = runComposeUiTest {
        val sessionId1 = UUID.randomUUID()
        val valueId1 = UUID.randomUUID()
        val valueId2 = UUID.randomUUID()

        val pendingUpstreamSessionValues = mutableStateListOf<Pair<SessionValue<Float>, SessionValue<Float>>>()

        lateinit var sessionValueHolder: SessionValueHolder<Float>
        var upstreamSessionValue by mutableStateOf(SessionValue(sessionId1, valueId1, 0f))

        setContent {
            sessionValueHolder = rememberSessionValueHolder(
                upstreamSessionValue = upstreamSessionValue,
                setUpstreamSessionValue = { upstreamSessionId, sessionValue ->
                    pendingUpstreamSessionValues.add(upstreamSessionId to sessionValue)
                },
            )
        }

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
        val nextSessionId1 = info1.nextSessionId
        assertEquals(nextSessionId1, info1.localSessionId)

        upstreamSessionValue = SessionValue(sessionId1, valueId2, 1f)
        waitForIdle()

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
        val nextSessionId2 = info2.nextSessionId
        assertEquals(nextSessionId2, info2.nextSessionId)
        assertEquals(nextSessionId2, info2.localSessionId)

        // Updating the upstream session value should cycle the next session id
        assertNotEquals(nextSessionId1, nextSessionId2)
    }

    @Test
    fun whenUpstreamSessionIdUpdated_stateMatches() = runComposeUiTest {
        val sessionId1 = UUID.randomUUID()
        val sessionId2 = UUID.randomUUID()
        val valueId1 = UUID.randomUUID()
        val valueId2 = UUID.randomUUID()

        val pendingUpstreamSessionValues = mutableStateListOf<Pair<SessionValue<Float>, SessionValue<Float>>>()

        lateinit var sessionValueHolder: SessionValueHolder<Float>
        var upstreamSessionValue by mutableStateOf(SessionValue(sessionId1, valueId1, 0f))

        setContent {
            sessionValueHolder = rememberSessionValueHolder(
                upstreamSessionValue = upstreamSessionValue,
                setUpstreamSessionValue = { upstreamSessionId, sessionValue ->
                    pendingUpstreamSessionValues.add(upstreamSessionId to sessionValue)
                },
            )
        }

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
        val nextSessionId1 = info1.nextSessionId
        assertEquals(nextSessionId1, info1.localSessionId)

        upstreamSessionValue = SessionValue(sessionId2, valueId2, 1f)
        waitForIdle()

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
        val nextSessionId2 = info2.nextSessionId
        assertEquals(nextSessionId2, info2.nextSessionId)
        assertEquals(nextSessionId2, info2.localSessionId)

        // Updating the upstream session value should cycle the next session id
        assertNotEquals(nextSessionId1, nextSessionId2)
    }

    @Test
    fun whenCreatingLocalSession_stateIsCorrect() = runComposeUiTest {
        val sessionId1 = UUID.randomUUID()
        val valueId1 = UUID.randomUUID()
        val valueId2 = UUID.randomUUID()

        val pendingUpstreamSessionValues = mutableStateListOf<Pair<SessionValue<Float>, SessionValue<Float>>>()

        lateinit var sessionValueHolder: SessionValueHolder<Float>
        val upstreamSessionValue by mutableStateOf(SessionValue(sessionId1, valueId1, 0f))

        setContent {
            sessionValueHolder = rememberSessionValueHolder(
                upstreamSessionValue = upstreamSessionValue,
                setUpstreamSessionValue = { upstreamSessionId, sessionValue ->
                    pendingUpstreamSessionValues.add(upstreamSessionId to sessionValue)
                },
            )
        }

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
        val nextSessionId1 = info1.nextSessionId
        assertEquals(nextSessionId1, info1.localSessionId)

        sessionValueHolder.setValue(1f, valueId2)
        waitForIdle()

        assertEquals(
            sessionValueHolder.sessionValue,
            SessionValue(
                nextSessionId1,
                valueId2,
                1f,
            ),
        )
        val info2 = sessionValueHolder.info
        assertTrue(info2.isLocalSessionActive())
        assertEquals(nextSessionId1, info2.currentSessionId)
        assertEquals(nextSessionId1, info2.localSessionId)
        assertFalse(info2.isUpstreamSessionValueUpToDate)
        assertEquals(
            listOf(
                SessionValue(sessionId1, valueId1, 0f) to SessionValue(nextSessionId1, valueId2, 1f),
            ),
            pendingUpstreamSessionValues,
        )
    }

    @Test
    fun localSessionActive_whenUpdatingValue_stateIsCorrect() = runComposeUiTest {
        val sessionId1 = UUID.randomUUID()
        val valueId1 = UUID.randomUUID()
        val valueId2 = UUID.randomUUID()
        val valueId3 = UUID.randomUUID()

        val pendingUpstreamSessionValues = mutableStateListOf<Pair<SessionValue<Float>, SessionValue<Float>>>()

        lateinit var sessionValueHolder: SessionValueHolder<Float>
        val upstreamSessionValue by mutableStateOf(SessionValue(sessionId1, valueId1, 0f))

        setContent {
            sessionValueHolder = rememberSessionValueHolder(
                upstreamSessionValue = upstreamSessionValue,
                setUpstreamSessionValue = { upstreamSessionId, sessionValue ->
                    pendingUpstreamSessionValues.add(upstreamSessionId to sessionValue)
                },
            )
        }

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
        val nextSessionId1 = info1.nextSessionId
        assertEquals(nextSessionId1, info1.localSessionId)

        sessionValueHolder.setValue(1f, valueId2)
        waitForIdle()

        assertEquals(
            sessionValueHolder.sessionValue,
            SessionValue(
                nextSessionId1,
                valueId2,
                1f,
            ),
        )
        val info2 = sessionValueHolder.info
        assertTrue(info2.isLocalSessionActive())
        assertEquals(nextSessionId1, info2.currentSessionId)
        assertEquals(nextSessionId1, info2.localSessionId)

        sessionValueHolder.setValue(2f, valueId3)
        waitForIdle()

        assertEquals(
            sessionValueHolder.sessionValue,
            SessionValue(
                nextSessionId1,
                valueId3,
                2f,
            ),
        )
        val info3 = sessionValueHolder.info
        assertTrue(info3.isLocalSessionActive())
        assertEquals(nextSessionId1, info3.currentSessionId)
        assertEquals(nextSessionId1, info3.localSessionId)
        assertFalse(info2.isUpstreamSessionValueUpToDate)
        assertEquals(
            listOf(
                SessionValue(sessionId1, valueId1, 0f) to SessionValue(nextSessionId1, valueId2, 1f),
                SessionValue(nextSessionId1, valueId2, 1f) to SessionValue(nextSessionId1, valueId3, 2f),
            ),
            pendingUpstreamSessionValues,
        )
    }

    @Test
    fun localSessionActive_whenUpstreamSessionCatchesUp_stateIsCorrect() = runComposeUiTest {
        val sessionId1 = UUID.randomUUID()
        val valueId1 = UUID.randomUUID()
        val valueId2 = UUID.randomUUID()

        val pendingUpstreamSessionValues = mutableStateListOf<Pair<SessionValue<Float>, SessionValue<Float>>>()

        lateinit var sessionValueHolder: SessionValueHolder<Float>
        var upstreamSessionValue by mutableStateOf(SessionValue(sessionId1, valueId1, 0f))

        setContent {
            sessionValueHolder = rememberSessionValueHolder(
                upstreamSessionValue = upstreamSessionValue,
                setUpstreamSessionValue = { upstreamSessionId, sessionValue ->
                    pendingUpstreamSessionValues.add(upstreamSessionId to sessionValue)
                },
            )
        }

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
        val nextSessionId1 = info1.nextSessionId
        assertEquals(nextSessionId1, info1.localSessionId)

        sessionValueHolder.setValue(1f, valueId2)
        waitForIdle()

        assertEquals(
            sessionValueHolder.sessionValue,
            SessionValue(
                nextSessionId1,
                valueId2,
                1f,
            ),
        )
        val info2 = sessionValueHolder.info
        assertTrue(info2.isLocalSessionActive())
        assertEquals(nextSessionId1, info2.currentSessionId)
        assertEquals(nextSessionId1, info2.localSessionId)
        assertFalse(info2.isUpstreamSessionValueUpToDate)
        assertEquals(
            listOf(
                SessionValue(sessionId1, valueId1, 0f) to SessionValue(nextSessionId1, valueId2, 1f),
            ),
            pendingUpstreamSessionValues,
        )

        upstreamSessionValue = pendingUpstreamSessionValues.removeFirst().second
        waitForIdle()

        assertEquals(
            sessionValueHolder.sessionValue,
            SessionValue(
                nextSessionId1,
                valueId2,
                1f,
            ),
        )
        val info3 = sessionValueHolder.info
        assertTrue(info3.isLocalSessionActive())
        assertEquals(nextSessionId1, info3.currentSessionId)
        assertEquals(nextSessionId1, info3.localSessionId)
        assertTrue(info3.isUpstreamSessionValueUpToDate)
        assertEquals(
            emptyList(),
            pendingUpstreamSessionValues,
        )
    }

    @Test
    fun localSessionActive_whenUpstreamSessionCatchesUpWithTwoChanges_stateIsCorrect() = runComposeUiTest {
        val sessionId1 = UUID.randomUUID()
        val valueId1 = UUID.randomUUID()
        val valueId2 = UUID.randomUUID()
        val valueId3 = UUID.randomUUID()

        val pendingUpstreamSessionValues = mutableStateListOf<Pair<SessionValue<Float>, SessionValue<Float>>>()

        lateinit var sessionValueHolder: SessionValueHolder<Float>
        var upstreamSessionValue by mutableStateOf(SessionValue(sessionId1, valueId1, 0f))

        setContent {
            sessionValueHolder = rememberSessionValueHolder(
                upstreamSessionValue = upstreamSessionValue,
                setUpstreamSessionValue = { upstreamSessionId, sessionValue ->
                    pendingUpstreamSessionValues.add(upstreamSessionId to sessionValue)
                },
            )
        }

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
        val nextSessionId1 = info1.nextSessionId
        assertEquals(nextSessionId1, info1.localSessionId)

        sessionValueHolder.setValue(1f, valueId2)
        waitForIdle()

        assertEquals(
            sessionValueHolder.sessionValue,
            SessionValue(
                nextSessionId1,
                valueId2,
                1f,
            ),
        )
        val info2 = sessionValueHolder.info
        assertTrue(info2.isLocalSessionActive())
        assertEquals(nextSessionId1, info2.currentSessionId)
        assertEquals(nextSessionId1, info2.localSessionId)
        assertFalse(info2.isUpstreamSessionValueUpToDate)
        assertEquals(
            listOf(
                SessionValue(sessionId1, valueId1, 0f) to SessionValue(nextSessionId1, valueId2, 1f),
            ),
            pendingUpstreamSessionValues,
        )

        sessionValueHolder.setValue(2f, valueId3)
        waitForIdle()

        assertEquals(
            sessionValueHolder.sessionValue,
            SessionValue(
                nextSessionId1,
                valueId3,
                2f,
            ),
        )
        val info3 = sessionValueHolder.info
        assertTrue(info3.isLocalSessionActive())
        assertEquals(nextSessionId1, info3.currentSessionId)
        assertEquals(nextSessionId1, info3.localSessionId)
        assertFalse(info2.isUpstreamSessionValueUpToDate)
        assertEquals(
            listOf(
                SessionValue(sessionId1, valueId1, 0f) to SessionValue(nextSessionId1, valueId2, 1f),
                SessionValue(nextSessionId1, valueId2, 1f) to SessionValue(nextSessionId1, valueId3, 2f),
            ),
            pendingUpstreamSessionValues,
        )

        upstreamSessionValue = pendingUpstreamSessionValues.removeFirst().second
        waitForIdle()

        assertEquals(
            sessionValueHolder.sessionValue,
            SessionValue(
                nextSessionId1,
                valueId3,
                2f,
            ),
        )
        val info4 = sessionValueHolder.info
        assertTrue(info4.isLocalSessionActive())
        assertEquals(nextSessionId1, info4.currentSessionId)
        assertEquals(nextSessionId1, info4.localSessionId)
        assertFalse(info4.isUpstreamSessionValueUpToDate)
        assertEquals(
            listOf(
                SessionValue(nextSessionId1, valueId2, 1f) to SessionValue(nextSessionId1, valueId3, 2f),
            ),
            pendingUpstreamSessionValues,
        )

        upstreamSessionValue = pendingUpstreamSessionValues.removeFirst().second
        waitForIdle()

        assertEquals(
            sessionValueHolder.sessionValue,
            SessionValue(
                nextSessionId1,
                valueId3,
                2f,
            ),
        )
        val info5 = sessionValueHolder.info
        assertTrue(info5.isLocalSessionActive())
        assertEquals(nextSessionId1, info5.currentSessionId)
        assertEquals(nextSessionId1, info5.localSessionId)
        assertTrue(info5.isUpstreamSessionValueUpToDate)
        assertEquals(
            emptyList(),
            pendingUpstreamSessionValues,
        )
    }

    @Test
    fun localSessionActive_whenUpstreamSessionChanges_stateIsCorrect() = runComposeUiTest {
        val sessionId1 = UUID.randomUUID()
        val sessionId2 = UUID.randomUUID()
        val valueId1 = UUID.randomUUID()
        val valueId2 = UUID.randomUUID()
        val valueId3 = UUID.randomUUID()

        val pendingUpstreamSessionValues = mutableStateListOf<Pair<SessionValue<Float>, SessionValue<Float>>>()

        lateinit var sessionValueHolder: SessionValueHolder<Float>
        var upstreamSessionValue by mutableStateOf(SessionValue(sessionId1, valueId1, 0f))

        setContent {
            sessionValueHolder = rememberSessionValueHolder(
                upstreamSessionValue = upstreamSessionValue,
                setUpstreamSessionValue = { upstreamSessionId, sessionValue ->
                    pendingUpstreamSessionValues.add(upstreamSessionId to sessionValue)
                },
            )
        }

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
        val nextSessionId1 = info1.nextSessionId
        assertEquals(nextSessionId1, info1.localSessionId)

        sessionValueHolder.setValue(1f, valueId2)
        waitForIdle()

        assertEquals(
            sessionValueHolder.sessionValue,
            SessionValue(
                nextSessionId1,
                valueId2,
                1f,
            ),
        )
        val info2 = sessionValueHolder.info
        assertTrue(info2.isLocalSessionActive())
        assertEquals(nextSessionId1, info2.currentSessionId)
        assertEquals(nextSessionId1, info2.localSessionId)
        assertFalse(info2.isUpstreamSessionValueUpToDate)
        assertEquals(
            listOf(
                SessionValue(sessionId1, valueId1, 0f) to SessionValue(nextSessionId1, valueId2, 1f),
            ),
            pendingUpstreamSessionValues,
        )

        upstreamSessionValue = SessionValue(
            sessionId2,
            valueId3,
            1f,
        )
        waitForIdle()

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
        val nextSessionId2 = info3.nextSessionId
        assertEquals(nextSessionId2, info3.localSessionId)

        // Updating the upstream session value should cycle the next session id
        assertNotEquals(nextSessionId1, nextSessionId2)
    }

    @Test
    fun localSessionActive_whenUpstreamSessionChangesBeforeLocalSession_stateIsCorrect() = runComposeUiTest {
        val sessionId1 = UUID.randomUUID()
        val valueId1 = UUID.randomUUID()
        val valueId2 = UUID.randomUUID()
        val valueId3 = UUID.randomUUID()

        val pendingUpstreamSessionValues = mutableStateListOf<Pair<SessionValue<Float>, SessionValue<Float>>>()

        lateinit var sessionValueHolder: SessionValueHolder<Float>
        var upstreamSessionValue by mutableStateOf(SessionValue(sessionId1, valueId1, 0f))

        setContent {
            sessionValueHolder = rememberSessionValueHolder(
                upstreamSessionValue = upstreamSessionValue,
                setUpstreamSessionValue = { upstreamSessionId, sessionValue ->
                    pendingUpstreamSessionValues.add(upstreamSessionId to sessionValue)
                },
            )
        }

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
        val nextSessionId1 = info1.nextSessionId
        assertEquals(nextSessionId1, info1.localSessionId)

        sessionValueHolder.setValue(1f, valueId2)
        waitForIdle()

        assertEquals(
            sessionValueHolder.sessionValue,
            SessionValue(
                nextSessionId1,
                valueId2,
                1f,
            ),
        )
        val info2 = sessionValueHolder.info
        assertTrue(info2.isLocalSessionActive())
        assertEquals(nextSessionId1, info2.currentSessionId)
        assertEquals(nextSessionId1, info2.localSessionId)
        assertFalse(info2.isUpstreamSessionValueUpToDate)
        assertEquals(
            listOf(
                SessionValue(sessionId1, valueId1, 0f) to SessionValue(nextSessionId1, valueId2, 1f),
            ),
            pendingUpstreamSessionValues,
        )

        upstreamSessionValue = SessionValue(
            sessionId1,
            valueId3,
            2f,
        )
        waitForIdle()

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
        val nextSessionId2 = info3.nextSessionId
        assertEquals(nextSessionId2, info3.localSessionId)

        // Updating the upstream session value should cycle the next session id
        assertNotEquals(nextSessionId1, nextSessionId2)
    }

    @Test
    fun whenSavedInstanceStateIsRestoredWithNoLocalSession_stateIsCorrect() = runComposeUiTest {
        val stateRestorationTester = KmpStateRestorationTester(this)

        val sessionId1 = UUID.randomUUID()
        val valueId1 = UUID.randomUUID()

        val pendingUpstreamSessionValues = mutableStateListOf<Pair<SessionValue<Float>, SessionValue<Float>>>()

        lateinit var sessionValueHolder: SessionValueHolder<Float>
        val upstreamSessionValue by mutableStateOf(SessionValue(sessionId1, valueId1, 0f))

        stateRestorationTester.setContent {
            sessionValueHolder = rememberSessionValueHolder(
                upstreamSessionValue = upstreamSessionValue,
                setUpstreamSessionValue = { upstreamSessionId, sessionValue ->
                    pendingUpstreamSessionValues.add(upstreamSessionId to sessionValue)
                },
            )
        }

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
        val nextSessionId1 = info1.nextSessionId
        assertEquals(nextSessionId1, info1.localSessionId)

        stateRestorationTester.emulateSavedInstanceStateRestore()
        waitForIdle()

        assertEquals(
            sessionValueHolder.sessionValue,
            SessionValue(
                sessionId1,
                valueId1,
                0f,
            ),
        )
        val info2 = sessionValueHolder.info
        assertFalse(info2.isLocalSessionActive())
        val nextSessionId2 = info1.nextSessionId
        assertEquals(nextSessionId1, info2.localSessionId)
        assertEquals(nextSessionId1, nextSessionId2)
    }

    @Test
    fun whenSavedInstanceStateIsRestoredWithLocalSession_stateIsCorrect() = runComposeUiTest {
        val stateRestorationTester = KmpStateRestorationTester(this)

        val sessionId1 = UUID.randomUUID()
        val valueId1 = UUID.randomUUID()
        val valueId2 = UUID.randomUUID()

        val pendingUpstreamSessionValues = mutableStateListOf<Pair<SessionValue<Float>, SessionValue<Float>>>()

        lateinit var sessionValueHolder: SessionValueHolder<Float>
        val upstreamSessionValue by mutableStateOf(SessionValue(sessionId1, valueId1, 0f))

        stateRestorationTester.setContent {
            sessionValueHolder = rememberSessionValueHolder(
                upstreamSessionValue = upstreamSessionValue,
                setUpstreamSessionValue = { upstreamSessionId, sessionValue ->
                    pendingUpstreamSessionValues.add(upstreamSessionId to sessionValue)
                },
            )
        }

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
        val nextSessionId1 = info1.nextSessionId
        assertEquals(nextSessionId1, info1.localSessionId)

        sessionValueHolder.setValue(1f, valueId2)
        waitForIdle()

        assertEquals(
            sessionValueHolder.sessionValue,
            SessionValue(
                nextSessionId1,
                valueId2,
                1f,
            ),
        )
        val info2 = sessionValueHolder.info
        assertTrue(info2.isLocalSessionActive())
        assertEquals(nextSessionId1, info2.currentSessionId)
        assertEquals(nextSessionId1, info2.localSessionId)

        stateRestorationTester.emulateSavedInstanceStateRestore()
        waitForIdle()

        assertEquals(
            sessionValueHolder.sessionValue,
            SessionValue(
                nextSessionId1,
                valueId2,
                1f,
            ),
        )
        val info3 = sessionValueHolder.info
        assertTrue(info3.isLocalSessionActive())
        assertEquals(nextSessionId1, info3.currentSessionId)
        assertEquals(nextSessionId1, info3.localSessionId)
    }

    @Test
    fun upstreamSessionChanges_whenSavedInstanceStateIsRestoredWithLocalSession_resetsSession() = runComposeUiTest {
        val stateRestorationTester = KmpStateRestorationTester(this)

        val sessionId1 = UUID.randomUUID()
        val sessionId2 = UUID.randomUUID()
        val valueId1 = UUID.randomUUID()
        val valueId2 = UUID.randomUUID()
        val valueId3 = UUID.randomUUID()

        val pendingUpstreamSessionValues = mutableStateListOf<Pair<SessionValue<Float>, SessionValue<Float>>>()

        lateinit var sessionValueHolder: SessionValueHolder<Float>

        var restorationCount by mutableStateOf(0)

        stateRestorationTester.setContent {
            DisposableEffect(Unit) {
                onDispose {
                    restorationCount++
                }
            }
            val upstreamSessionValue = when (restorationCount) {
                0 -> SessionValue(sessionId1, valueId1, 0f)
                1 -> SessionValue(sessionId2, valueId3, 2f)
                else -> fail("Unexpected restoration count!")
            }

            sessionValueHolder = rememberSessionValueHolder(
                upstreamSessionValue = upstreamSessionValue,
                setUpstreamSessionValue = { upstreamSessionId, sessionValue ->
                    pendingUpstreamSessionValues.add(upstreamSessionId to sessionValue)
                },
            )
        }

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
        val nextSessionId1 = info1.nextSessionId
        assertEquals(nextSessionId1, info1.localSessionId)

        sessionValueHolder.setValue(1f, valueId2)
        waitForIdle()

        assertEquals(
            sessionValueHolder.sessionValue,
            SessionValue(
                nextSessionId1,
                valueId2,
                1f,
            ),
        )
        val info2 = sessionValueHolder.info
        assertTrue(info2.isLocalSessionActive())
        assertEquals(nextSessionId1, info2.currentSessionId)
        assertEquals(nextSessionId1, info2.localSessionId)

        stateRestorationTester.emulateSavedInstanceStateRestore()
        waitForIdle()

        assertEquals(
            sessionValueHolder.sessionValue,
            SessionValue(
                sessionId2,
                valueId3,
                2f,
            ),
        )
        val info3 = sessionValueHolder.info
        assertFalse(info3.isLocalSessionActive())
        val nextSessionId2 = info3.nextSessionId
        assertEquals(nextSessionId2, info3.localSessionId)

        // Updating the upstream session value should cycle the next session id
        assertNotEquals(nextSessionId1, nextSessionId2)
    }
}
