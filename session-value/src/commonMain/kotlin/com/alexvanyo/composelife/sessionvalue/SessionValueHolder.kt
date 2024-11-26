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

import androidx.compose.runtime.Composable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.saveable.Saver
import androidx.compose.runtime.saveable.autoSaver
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import com.alexvanyo.composelife.serialization.uuidSaver
import kotlin.uuid.Uuid

/**
 * A multiplexer for a [SessionValue] that can maintain the state for a local session that runs ahead of the
 * upstream [SessionValue].
 *
 * The [sessionValue] will match the upstream session value passed to [rememberSessionValueHolder], until
 * [setValue] is called.
 *
 * Once [setValue] is called, the [sessionValue] will run ahead of the upstream [SessionValue].
 *
 * [info] contains additional status information about the local session.
 */
sealed interface SessionValueHolder<T> {
    val sessionValue: SessionValue<T>
    val info: LocalSessionInfo

    /**
     * Sets the value upstream via the [SessionValueHolder], and begins (or continues) a local session.
     */
    fun setValue(
        value: T,
        valueId: Uuid = Uuid.random(),
    )
}

/**
 * A multiplexer for a [SessionValue] that can maintain the state for a local session that runs ahead of the
 * upstream [SessionValue].
 *
 * The [SessionValueHolder.sessionValue] will match the [upstreamSessionValue] until [SessionValueHolder.setValue]
 * is called.
 *
 * Once [SessionValueHolder.setValue] is called, the [SessionValueHolder.sessionValue] will be representing a local
 * session that may be ahead of what the upstream value shows. [setUpstreamSessionValue] will be called from
 * [SessionValueHolder.setValue], and begin updating the upstream value in tandem with keeping a local state in
 * [SessionValueHolder.sessionValue].
 *
 * [SessionValueHolder.info] returns information about the current local session, if any.
 * In particular [LocalSessionInfo.localSessionId] will returns the session id that will be used to represent
 * the local session when [SessionValueHolder.setValue] is called.
 *
 * [SessionValueHolder] supports cases where the [upstreamSessionValue] changes independently from the local session. In
 * those cases, the internal state will be reset to match the [upstreamSessionValue].
 */
@Composable
fun <T> rememberSessionValueHolder(
    /**
     * The upstream [SessionValue].
     */
    upstreamSessionValue: SessionValue<T>,
    /**
     * Sets the upstream [SessionValue] to the given [SessionValue].
     * The provided upstream session id is the known previous id, for a compare-and-set updating of the [SessionValue].
     */
    setUpstreamSessionValue: (expected: SessionValue<T>, newValue: SessionValue<T>) -> Unit,
    valueSaver: Saver<T, *> = autoSaver(),
): SessionValueHolder<T> =
    rememberSaveable(
        saver = SessionValueHolderImpl.Saver(
            initialSetUpstreamSessionValue = setUpstreamSessionValue,
            valueSaver = valueSaver,
        ),
    ) {
        SessionValueHolderImpl(
            initialUpstreamSessionValue = upstreamSessionValue,
            initialSetUpstreamSessionValue = setUpstreamSessionValue,
            initialLocalSessionId = Uuid.random(),
            initialLocalSessionValue = null,
            initialUpstreamSessionIdBeforeLocalSession = upstreamSessionValue.sessionId,
        )
    }
        .apply {
            setValueFromUpstream(upstreamSessionValue)
            this.setUpstreamSessionValue = setUpstreamSessionValue
        }

private class SessionValueHolderImpl<T>(
    initialUpstreamSessionIdBeforeLocalSession: Uuid,
    initialUpstreamSessionValue: SessionValue<T>,
    initialSetUpstreamSessionValue: (expected: SessionValue<T>, newValue: SessionValue<T>) -> Unit,
    initialLocalSessionId: Uuid,
    initialLocalSessionValue: SessionValue<T>?,
) : SessionValueHolder<T> {
    /**
     * The upstream session id known prior to the current local session (if any).
     */
    var upstreamSessionIdBeforeLocalSession by mutableStateOf(initialUpstreamSessionIdBeforeLocalSession)

    /**
     * The current known upstream session value.
     */
    var upstreamSessionValue by mutableStateOf(initialUpstreamSessionValue)

    /**
     * The local session id for the current local session (if any), otherwise the local session id that will be used
     * for the next local session.
     */
    var localSessionId: Uuid by mutableStateOf(initialLocalSessionId)

    /**
     * If non-null, the local session value that is set and is running ahead of the [upstreamSessionValue].
     */
    var localSessionValue: SessionValue<T>? by mutableStateOf(initialLocalSessionValue)

    var setUpstreamSessionValue by mutableStateOf(initialSetUpstreamSessionValue)

    override val sessionValue: SessionValue<T>
        get() = localSessionValue ?: upstreamSessionValue

    override val info: LocalSessionInfo
        get() {
            val currentLocalSessionValue = localSessionValue
            return if (currentLocalSessionValue == null) {
                check(upstreamSessionIdBeforeLocalSession == upstreamSessionValue.sessionId)
                LocalSessionInfo.Inactive(
                    currentUpstreamSessionId = upstreamSessionValue.sessionId,
                    nextLocalSessionId = localSessionId,
                )
            } else {
                LocalSessionInfo.Active(
                    currentLocalSessionId = localSessionId,
                    isUpstreamSessionValueUpToDate =
                    upstreamSessionValue.sessionId == currentLocalSessionValue.sessionId &&
                        upstreamSessionValue.valueId == currentLocalSessionValue.valueId,
                    previousUpstreamSessionId = upstreamSessionIdBeforeLocalSession,
                )
            }
        }

    override fun setValue(
        value: T,
        valueId: Uuid,
    ) {
        val expected = sessionValue
        localSessionValue = SessionValue(
            sessionId = localSessionId,
            valueId = valueId,
            value = value,
        )
        setUpstreamSessionValue(expected, sessionValue)
    }

    /**
     * Synchronizes the internal state from the upstream [SessionValue].
     */
    fun setValueFromUpstream(
        newUpstreamSessionValue: SessionValue<T>,
    ) {
        val hasSessionValueChanged =
            newUpstreamSessionValue.sessionId != upstreamSessionValue.sessionId ||
                newUpstreamSessionValue.valueId != upstreamSessionValue.valueId

        // If our most recent upstream session value still matches this new one, we have nothing to do
        if (hasSessionValueChanged) {
            // Otherwise, we've seen a new upstream session value
            if (newUpstreamSessionValue.sessionId != localSessionValue?.sessionId) {
                // The upstream session has become something different than the local session (if any) and the session
                // value before our local session. Clear the local session, to revert back to the new upstream session.
                localSessionId = Uuid.random()
                localSessionValue = null
            }
            // Update the previous upstream session id in all cases except when we are see the update to our local
            // session id
            if (localSessionId != newUpstreamSessionValue.sessionId) {
                upstreamSessionIdBeforeLocalSession = newUpstreamSessionValue.sessionId
            }
            upstreamSessionValue = newUpstreamSessionValue
        }
    }

    companion object {
        fun <T> Saver(
            initialSetUpstreamSessionValue: (expected: SessionValue<T>, newValue: SessionValue<T>) -> Unit,
            valueSaver: Saver<T, *>,
        ): Saver<SessionValueHolderImpl<T>, *> {
            val sessionValueSaver = SessionValue.Saver(valueSaver)

            return Saver(
                save = {
                    listOf(
                        with(uuidSaver) {
                            save(it.localSessionId)
                        },
                        with(sessionValueSaver) {
                            it.localSessionValue?.let { localSessionValue -> save(localSessionValue) }
                        },
                        with(sessionValueSaver) {
                            save(it.upstreamSessionValue)
                        },
                        with(uuidSaver) {
                            save(it.upstreamSessionIdBeforeLocalSession)
                        },
                    )
                },
                restore = {
                    SessionValueHolderImpl(
                        initialUpstreamSessionIdBeforeLocalSession = uuidSaver.restore(it[3] as String)!!,
                        initialUpstreamSessionValue = sessionValueSaver.restore(it[2]!!)!!,
                        initialSetUpstreamSessionValue = initialSetUpstreamSessionValue,
                        initialLocalSessionId = uuidSaver.restore(it[0] as String)!!,
                        initialLocalSessionValue = it[1]?.let(sessionValueSaver::restore),
                    )
                },
            )
        }
    }
}
