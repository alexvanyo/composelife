/*
 * Copyright 2023 The Android Open Source Project
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

package com.alexvanyo.composelife.updatable

import kotlinx.coroutines.CompletableDeferred
import kotlinx.coroutines.Deferred
import kotlinx.coroutines.Job
import kotlinx.coroutines.awaitCancellation
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.coroutineScope
import kotlinx.coroutines.flow.update
import kotlinx.coroutines.launch
import kotlinx.coroutines.selects.select
import kotlinx.coroutines.sync.Mutex
import kotlinx.coroutines.sync.withLock

/**
 * An implementation of [Updatable] that resembles a button that can be powered, and pressed by multiple coroutines
 * simultaneously to control running a given [block] with mutual exclusion.
 *
 * Calling [update] will "power" the button, which will not run the [block] on its own.
 *
 * When the button is pressed and powered (due to an active coroutine calling [update], and at least one coroutine
 * calling [press]), the [block] will begin to run.
 *
 * Pressing the button more than once has no effect.
 *
 * [block] will be cancelled if the button is no longer being pressed at all, or when the call to [update] is
 * cancelled.
 */
class PowerableUpdatable(
    private val block: suspend () -> Nothing,
) : Updatable {
    private val mutex = Mutex()

    private val activePushesMutex = Mutex()
    private val activePushes = mutableListOf<Deferred<Nothing>>()

    private val newActivePushesTick = Channel<Unit>(capacity = Channel.CONFLATED)

    /**
     * "Powers" the button, allowing the [block] to run if [press]ed.
     *
     * This does nothing unless the button is also pressed via [press].
     *
     * Multiple calls to [update] to power the button are safe, _but_ if the source of power is replaced, the [block]
     * will be cancelled and restarted.
     */
    override suspend fun update(): Nothing =
        mutex.withLock {
            coroutineScope {
                var job: Job? = null

                while (true) {
                    // Keep the list of active pushes that we know about
                    val currentlyActivePushes: List<Deferred<Nothing>>
                    activePushesMutex.withLock {
                        // Remove any pushes that have been cancelled
                        // We do this on both sides to avoid leaking if pressing and unpressing the button
                        // repeatedly without being powered
                        activePushes.removeIf { it.isCompleted }
                        currentlyActivePushes = activePushes

                        if (currentlyActivePushes.isEmpty()) {
                            // If we are no longer being pushed at all, cancel and clear out the job running the block
                            job?.cancel()
                            job = null
                        } else if (job == null) {
                            // If we are actively pushing and we don't have an existing job, launch the block
                            job = launch { block() }
                        }
                    }

                    // Wait for a new active push, or for any of the existing pushes to be cancelled.
                    select {
                        newActivePushesTick.onReceive {}
                        currentlyActivePushes.forEach { it.onJoin {} }
                    }
                }

                @Suppress("UNREACHABLE_CODE")
                error("loop can not complete normally")
            }
        }

    /**
     * Presses the button.
     *
     * This does nothing unless the button is also "powered" via [update].
     *
     * Multiple calls to [press] are safe, and the running of [block] will not be interrupted if the source of pressing
     * is replaced (as long as the presses overlap).
     */
    suspend fun press(): Nothing {
        val push = CompletableDeferred<Nothing>()
        try {
            activePushesMutex.withLock {
                // Send the tick first to wake up update
                // It won't be able to run until we exit the lock
                // This guards against adding our push, but failing to notify update that it was added if cancelled
                // immediately.
                newActivePushesTick.send(Unit)

                // Remove any pushes that have been cancelled
                // We do this on both sides to avoid leaking if pressing and unpressing the button
                // repeatedly without being powered
                activePushes.removeIf { it.isCompleted }
                activePushes.add(push)
            }
            awaitCancellation()
        } finally {
            push.cancel()
        }
    }
}
