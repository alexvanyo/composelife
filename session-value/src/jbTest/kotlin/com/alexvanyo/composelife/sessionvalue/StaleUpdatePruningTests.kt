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

import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue
import kotlin.uuid.Uuid

class StaleUpdatePruningTests {

    @Test
    fun whenSessionInvalidatedBySameUpstreamSession_staleFirstUpdateIsRemoved() {
        val upstreamSessionId = Uuid.random()
        val baseValue = SessionValue(upstreamSessionId, Uuid.random(), 0f)
        val foreignValue = SessionValue(upstreamSessionId, Uuid.random(), 5f)

        val initialState = SessionValueState(
            upstreamSessionIdBeforeLocalSession = upstreamSessionId,
            upstreamSessionValue = baseValue,
            localSessionId = Uuid.random(),
            localSessionValue = null,
        )
        // The first edit is still queued when the same upstream session writes again
        val (afterFirstEdit, firstUpdate) = initialState.stepSetValue(1f, Uuid.random())
        val afterForeignWrite = afterFirstEdit.stepSetValueFromUpstream(foreignValue, Uuid.random())
        // The second edit, in the new local session, is queued before the queue is flushed
        val (afterSecondEdit, secondUpdate) = afterForeignWrite.stepSetValue(2f, Uuid.random())

        // The stale first update expects a value from the new pre-local session
        assertEquals(afterSecondEdit.info.preLocalSessionId, firstUpdate.first.sessionId)

        val updates = mutableListOf(firstUpdate, secondUpdate)
        updates.removeStaleUpdates(afterSecondEdit.info)

        assertEquals(listOf(secondUpdate), updates)
        // The batched update now succeeds against the current upstream value
        assertEquals(foreignValue, updates.first().first)
        assertEquals(afterSecondEdit.sessionValue, updates.last().second)
    }

    @Test
    fun whenAllUpdatesAreFromCurrentSession_noUpdatesAreRemoved() {
        val upstreamSessionId = Uuid.random()
        val baseValue = SessionValue(upstreamSessionId, Uuid.random(), 0f)

        val initialState = SessionValueState(
            upstreamSessionIdBeforeLocalSession = upstreamSessionId,
            upstreamSessionValue = baseValue,
            localSessionId = Uuid.random(),
            localSessionValue = null,
        )
        val (afterFirstEdit, firstUpdate) = initialState.stepSetValue(1f, Uuid.random())
        val (afterSecondEdit, secondUpdate) = afterFirstEdit.stepSetValue(2f, Uuid.random())

        val updates = mutableListOf(firstUpdate, secondUpdate)
        updates.removeStaleUpdates(afterSecondEdit.info)

        assertEquals(listOf(firstUpdate, secondUpdate), updates)
    }

    @Test
    fun whenSessionInvalidatedWithoutNewEdits_allUpdatesAreRemoved() {
        val upstreamSessionId = Uuid.random()
        val baseValue = SessionValue(upstreamSessionId, Uuid.random(), 0f)
        val foreignValue = SessionValue(Uuid.random(), Uuid.random(), 5f)

        val initialState = SessionValueState(
            upstreamSessionIdBeforeLocalSession = upstreamSessionId,
            upstreamSessionValue = baseValue,
            localSessionId = Uuid.random(),
            localSessionValue = null,
        )
        val (afterFirstEdit, firstUpdate) = initialState.stepSetValue(1f, Uuid.random())
        val (afterSecondEdit, secondUpdate) = afterFirstEdit.stepSetValue(2f, Uuid.random())
        val afterForeignWrite = afterSecondEdit.stepSetValueFromUpstream(foreignValue, Uuid.random())

        val updates = mutableListOf(firstUpdate, secondUpdate)
        updates.removeStaleUpdates(afterForeignWrite.info)

        assertTrue(updates.isEmpty())
    }
}
