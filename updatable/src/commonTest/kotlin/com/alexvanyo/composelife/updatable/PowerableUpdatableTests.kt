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

import app.cash.turbine.test
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.awaitCancellation
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.delay
import kotlinx.coroutines.flow.receiveAsFlow
import kotlinx.coroutines.launch
import kotlinx.coroutines.test.runTest
import kotlin.test.Test
import kotlin.test.assertEquals

@OptIn(ExperimentalCoroutinesApi::class)
class PowerableUpdatableTests {

    @Test
    fun powered_block_does_not_run() = runTest {
        val runningEvents = Channel<Boolean>(capacity = Channel.UNLIMITED)

        val powerableUpdatable = PowerableUpdatable {
            runningEvents.trySend(true)
            try {
                awaitCancellation()
            } finally {
                runningEvents.trySend(false)
            }
        }

        runningEvents.receiveAsFlow().test {
            val updateJob = launch {
                powerableUpdatable.update()
            }

            delay(100)
            expectNoEvents()

            cancel()
            updateJob.cancel()
        }
    }

    @Test
    fun powered_and_pressed_block_runs() = runTest {
        val runningEvents = Channel<Boolean>(capacity = Channel.UNLIMITED)

        val powerableUpdatable = PowerableUpdatable {
            runningEvents.trySend(true)
            try {
                awaitCancellation()
            } finally {
                runningEvents.trySend(false)
            }
        }

        runningEvents.receiveAsFlow().test {
            val updateJob = launch {
                powerableUpdatable.update()
            }

            expectNoEvents()

            val pressJob = launch {
                powerableUpdatable.press()
            }

            assertEquals(true, awaitItem())
            expectNoEvents()

            pressJob.cancel()
            assertEquals(false, awaitItem())
            expectNoEvents()

            cancel()
            updateJob.cancel()
        }
    }

    @Test
    fun powered_and_pressed_block_runs_once() = runTest {
        val runningEvents = Channel<Boolean>(capacity = Channel.UNLIMITED)

        val powerableUpdatable = PowerableUpdatable {
            runningEvents.trySend(true)
            try {
                awaitCancellation()
            } finally {
                runningEvents.trySend(false)
            }
        }

        runningEvents.receiveAsFlow().test {
            val updateJob = launch {
                powerableUpdatable.update()
            }

            expectNoEvents()

            val pressJob1 = launch {
                powerableUpdatable.press()
            }

            assertEquals(true, awaitItem())
            expectNoEvents()

            val pressJob2 = launch {
                powerableUpdatable.press()
            }

            expectNoEvents()

            pressJob1.cancel()

            expectNoEvents()

            pressJob2.cancel()

            assertEquals(false, awaitItem())
            expectNoEvents()

            cancel()
            updateJob.cancel()
        }
    }

    @Test
    fun powered_and_unpowered_runs_block_twice_when_still_pressed() = runTest {
        val runningEvents = Channel<Boolean>(capacity = Channel.UNLIMITED)

        val powerableUpdatable = PowerableUpdatable {
            runningEvents.trySend(true)
            try {
                awaitCancellation()
            } finally {
                runningEvents.trySend(false)
            }
        }

        runningEvents.receiveAsFlow().test {
            val updateJob1 = launch {
                powerableUpdatable.update()
            }

            val updateJob2 = launch {
                powerableUpdatable.update()
            }

            expectNoEvents()

            val pressJob = launch {
                powerableUpdatable.press()
            }

            assertEquals(true, awaitItem())
            expectNoEvents()

            updateJob1.cancel()

            assertEquals(false, awaitItem())
            assertEquals(true, awaitItem())
            expectNoEvents()

            pressJob.cancel()

            assertEquals(false, awaitItem())
            expectNoEvents()

            cancel()
            updateJob2.cancel()
        }
    }

    @Test
    fun pressed_and_powered_runs_block() = runTest {
        val runningEvents = Channel<Boolean>(capacity = Channel.UNLIMITED)

        val powerableUpdatable = PowerableUpdatable {
            runningEvents.trySend(true)
            try {
                awaitCancellation()
            } finally {
                runningEvents.trySend(false)
            }
        }

        runningEvents.receiveAsFlow().test {
            val pressJob = launch {
                powerableUpdatable.press()
            }

            expectNoEvents()

            val updateJob = launch {
                powerableUpdatable.update()
            }

            assertEquals(true, awaitItem())
            expectNoEvents()

            pressJob.cancel()

            assertEquals(false, awaitItem())
            expectNoEvents()

            cancel()
            updateJob.cancel()
        }
    }
}
