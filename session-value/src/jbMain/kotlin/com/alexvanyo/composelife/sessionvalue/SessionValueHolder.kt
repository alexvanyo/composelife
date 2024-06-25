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
import java.util.UUID
import kotlin.contracts.ExperimentalContracts
import kotlin.contracts.contract

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
        valueId: UUID = UUID.randomUUID(),
    )
}

/**
 * Information about a local session in a [SessionValueHolder].
 */
sealed interface LocalSessionInfo {

    /**
     * The local session is active, meaning that the session value is running ahead of the upstream value.
     */
    data class Active(
        /**
         * The current local session id.
         */
        val currentLocalSessionId: UUID,
        /**
         * If true, then the upstream value has caught up to the local session value.
         */
        val isUpstreamSessionValueUpToDate: Boolean,
        /**
         * The previous upstream session id. This was the session id that was replaced by this active
         * [currentLocalSessionId].
         */
        val previousUpstreamSessionId: UUID,
    ) : LocalSessionInfo

    /**
     * The local session is inactive, meaning that the session value is just matching the upstream value.
     */
    data class Inactive(
        /**
         * The current upstream session id.
         */
        val currentUpstreamSessionId: UUID,
        /**
         * [nextLocalSessionId] will be the local session id used when [SessionValueHolder.setValue] is next called
         * if the upstream does not change. This will be cycled whenever the upstream session changes id or value.
         */
        val nextLocalSessionId: UUID,
    ) : LocalSessionInfo
}

/**
 * The local session id that will remain constant when upgrading from [LocalSessionInfo.Inactive] to an
 * [LocalSessionInfo.Active].
 *
 * Use this as a key to fork an editing session off of a specific session and value.
 */
val LocalSessionInfo.localSessionId: UUID get() =
    when (this) {
        is LocalSessionInfo.Active -> currentLocalSessionId
        is LocalSessionInfo.Inactive -> nextLocalSessionId
    }

/**
 * The previous upstream session id that will remain constant when upgrading from [LocalSessionInfo.Inactive] to an
 * [LocalSessionInfo.Active].
 *
 * Use this as a key for tracking a previous session.
 */
val LocalSessionInfo.preLocalSessionId: UUID get() =
    when (this) {
        is LocalSessionInfo.Active -> previousUpstreamSessionId
        is LocalSessionInfo.Inactive -> currentUpstreamSessionId
    }

@OptIn(ExperimentalContracts::class)
fun LocalSessionInfo.isLocalSessionActive(): Boolean {
    contract {
        returns(true) implies (this@isLocalSessionActive is LocalSessionInfo.Active)
        returns(false) implies (this@isLocalSessionActive is LocalSessionInfo.Inactive)
    }
    return when (this) {
        is LocalSessionInfo.Active -> true
        is LocalSessionInfo.Inactive -> false
    }
}

private class SessionValueHolderImpl<T>(
    initialPreviousUpstreamSessionId: UUID,
    initialUpstreamSessionValue: SessionValue<T>,
    initialSetUpstreamSessionValue: (expected: SessionValue<T>, newValue: SessionValue<T>) -> Unit,
    initialLocalSessionId: UUID,
    initialLocalSessionValue: SessionValue<T>?,
) : SessionValueHolder<T> {
    var previousUpstreamSessionId by mutableStateOf(initialPreviousUpstreamSessionId)

    var upstreamSessionValue by mutableStateOf(initialUpstreamSessionValue)

    var localSessionId: UUID by mutableStateOf(initialLocalSessionId)

    var localSessionValue: SessionValue<T>? by mutableStateOf(initialLocalSessionValue)

    var setUpstreamSessionValue by mutableStateOf(initialSetUpstreamSessionValue)

    override val sessionValue: SessionValue<T>
        get() = localSessionValue ?: upstreamSessionValue

    override val info: LocalSessionInfo
        get() {
            val currentLocalSessionValue = localSessionValue
            return if (currentLocalSessionValue == null) {
                LocalSessionInfo.Inactive(
                    currentUpstreamSessionId = previousUpstreamSessionId,
                    nextLocalSessionId = localSessionId,
                )
            } else {
                LocalSessionInfo.Active(
                    currentLocalSessionId = localSessionId,
                    isUpstreamSessionValueUpToDate =
                    upstreamSessionValue.sessionId == currentLocalSessionValue.sessionId &&
                        upstreamSessionValue.valueId == currentLocalSessionValue.valueId,
                    previousUpstreamSessionId = previousUpstreamSessionId,
                )
            }
        }

    override fun setValue(
        value: T,
        valueId: UUID,
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
        sessionValue: SessionValue<T>,
    ) {
        val hasSessionValueChanged =
            sessionValue.sessionId != upstreamSessionValue.sessionId ||
                sessionValue.valueId != upstreamSessionValue.valueId

        if (!hasSessionValueChanged) {
            return
        }

        val currentLocalSessionValue = localSessionValue

        if (currentLocalSessionValue == null) {
            // The upstream session has changed. Cycle the local session, to indicate that any derived local state
            // should update.
            localSessionId = UUID.randomUUID()
        } else {
            if (sessionValue.sessionId != currentLocalSessionValue.sessionId) {
                // The upstream session has become something different than the local session and the session value
                // before our local session. Clear the local session, to revert back to the new upstream session.
                localSessionId = UUID.randomUUID()
                localSessionValue = null
            }
        }
        // Update the previous upstream session id in all cases except when we are see the update to our local session
        // id
        if (localSessionId != sessionValue.sessionId) {
            previousUpstreamSessionId = sessionValue.sessionId
        }
        upstreamSessionValue = sessionValue
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
                            save(it.previousUpstreamSessionId)
                        },
                    )
                },
                restore = {
                    SessionValueHolderImpl(
                        initialPreviousUpstreamSessionId = uuidSaver.restore(it[3] as String)!!,
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
            initialLocalSessionId = UUID.randomUUID(),
            initialLocalSessionValue = null,
            initialPreviousUpstreamSessionId = upstreamSessionValue.sessionId,
        )
    }
        .apply {
            setValueFromUpstream(upstreamSessionValue)
            this.setUpstreamSessionValue = setUpstreamSessionValue
        }
