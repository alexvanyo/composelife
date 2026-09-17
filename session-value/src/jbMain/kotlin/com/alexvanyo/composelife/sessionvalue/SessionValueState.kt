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

import androidx.compose.runtime.Immutable
import kotlinx.serialization.Serializable
import kotlin.uuid.Uuid

/**
 * Pure state machine representing the state of a session value holder.
 *
 * Matches `SessionValue.StateMachine` in the Lean 4 formal specification.
 */
@Immutable
@Serializable
data class SessionValueState<out T>(
    val upstreamSessionIdBeforeLocalSession: Uuid,
    val upstreamSessionValue: SessionValue<T>,
    val localSessionId: Uuid,
    val localSessionValue: SessionValue<T>?,
) {
    val sessionValue: SessionValue<T>
        get() = localSessionValue ?: upstreamSessionValue

    val info: LocalSessionInfo
        get() =
            when (val currentLocalSessionValue = localSessionValue) {
                null -> {
                    check(upstreamSessionIdBeforeLocalSession == upstreamSessionValue.sessionId)
                    LocalSessionInfo.Inactive(
                        currentUpstreamSessionId = upstreamSessionValue.sessionId,
                        nextLocalSessionId = localSessionId,
                    )
                }

                else -> {
                    LocalSessionInfo.Active(
                        currentLocalSessionId = localSessionId,
                        isUpstreamSessionValueUpToDate =
                        upstreamSessionValue.sessionId == currentLocalSessionValue.sessionId &&
                            upstreamSessionValue.valueId == currentLocalSessionValue.valueId,
                        previousUpstreamSessionId = upstreamSessionIdBeforeLocalSession,
                    )
                }
            }

    fun stepSetValue(
        value: @UnsafeVariance T,
        valueId: Uuid = Uuid.random(),
    ): Pair<SessionValueState<T>, Pair<SessionValue<T>, SessionValue<T>>> {
        val expected = sessionValue
        val newLocalVal = SessionValue(
            sessionId = localSessionId,
            valueId = valueId,
            value = value,
        )
        val nextState = copy(localSessionValue = newLocalVal)
        return nextState to (expected to newLocalVal)
    }

    fun stepSetValueFromUpstream(
        newUpstreamSessionValue: SessionValue<@UnsafeVariance T>,
        freshLocalSessionId: Uuid = Uuid.random(),
    ): SessionValueState<T> {
        val hasSessionValueChanged =
            newUpstreamSessionValue.sessionId != upstreamSessionValue.sessionId ||
                newUpstreamSessionValue.valueId != upstreamSessionValue.valueId

        if (!hasSessionValueChanged) {
            return this
        }

        val isDifferentSession = newUpstreamSessionValue.sessionId != localSessionValue?.sessionId
        val nextLocalSessionId = if (isDifferentSession) freshLocalSessionId else localSessionId
        val nextLocalSessionValue = if (isDifferentSession) null else localSessionValue
        val nextUpstreamBefore =
            if (nextLocalSessionId != newUpstreamSessionValue.sessionId) {
                newUpstreamSessionValue.sessionId
            } else {
                upstreamSessionIdBeforeLocalSession
            }

        return SessionValueState(
            upstreamSessionIdBeforeLocalSession = nextUpstreamBefore,
            upstreamSessionValue = newUpstreamSessionValue,
            localSessionId = nextLocalSessionId,
            localSessionValue = nextLocalSessionValue,
        )
    }
}
