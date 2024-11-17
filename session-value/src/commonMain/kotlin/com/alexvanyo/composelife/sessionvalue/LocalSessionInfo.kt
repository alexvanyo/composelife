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

import kotlin.contracts.ExperimentalContracts
import kotlin.contracts.contract
import kotlin.uuid.Uuid

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
        val currentLocalSessionId: Uuid,
        /**
         * If true, then the upstream value has caught up to the local session value.
         */
        val isUpstreamSessionValueUpToDate: Boolean,
        /**
         * The previous upstream session id. This was the session id that was replaced by this active
         * [currentLocalSessionId].
         */
        val previousUpstreamSessionId: Uuid,
    ) : LocalSessionInfo

    /**
     * The local session is inactive, meaning that the session value is just matching the upstream value.
     */
    data class Inactive(
        /**
         * The current upstream session id.
         */
        val currentUpstreamSessionId: Uuid,
        /**
         * [nextLocalSessionId] will be the local session id used when [SessionValueHolder.setValue] is next called
         * if the upstream does not change. This will be cycled whenever the upstream session changes id or value.
         */
        val nextLocalSessionId: Uuid,
    ) : LocalSessionInfo
}

/**
 * The local session id that will remain constant when upgrading from [LocalSessionInfo.Inactive] to an
 * [LocalSessionInfo.Active].
 *
 * Use this as a key to fork an editing session off of a specific session and value.
 */
val LocalSessionInfo.localSessionId: Uuid
    get() =
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
val LocalSessionInfo.preLocalSessionId: Uuid
    get() =
        when (this) {
            is LocalSessionInfo.Active -> previousUpstreamSessionId
            is LocalSessionInfo.Inactive -> currentUpstreamSessionId
        }

/**
 * Returns `true` if the [LocalSessionInfo] is [LocalSessionInfo.Active], and `false` if the [LocalSessionInfo]
 * is [LocalSessionInfo.Inactive].
 */
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
