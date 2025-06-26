/*
 * Copyright 2025 The Android Open Source Project
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

package com.alexvanyo.composelife.ui.util

import androidx.compose.runtime.BroadcastFrameClock
import app.cash.molecule.RecompositionMode
import app.cash.molecule.moleculeFlow
import app.cash.turbine.test
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.flow.distinctUntilChanged
import kotlinx.coroutines.test.StandardTestDispatcher
import kotlinx.coroutines.test.TestCoroutineScheduler
import kotlinx.coroutines.test.runCurrent
import kotlinx.coroutines.test.runTest
import kotlinx.datetime.DateTimePeriod
import kotlinx.datetime.DateTimeUnit
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.time.Clock
import kotlin.time.Duration
import kotlin.time.Duration.Companion.milliseconds
import kotlin.time.Duration.Companion.minutes
import kotlin.time.Duration.Companion.seconds
import kotlin.time.Instant

@OptIn(ExperimentalCoroutinesApi::class)
class PeriodUntilComposableTests {
    private val start = Instant.fromEpochMilliseconds(1741463473365L)
    private var now = start
    private val testScheduler = TestCoroutineScheduler()
    private val testDispatcher = StandardTestDispatcher(testScheduler)
    private val broadcastFrameClock = BroadcastFrameClock()
    private var nowInvokedCount = 0

    private val clock = object : Clock {
        override fun now(): Instant = now.also { nowInvokedCount++ }
    }

    private fun advanceTimeBy(duration: Duration) {
        now += duration
        testScheduler.advanceTimeBy(duration)
    }

    @Test
    fun period_until_time_based() = runTest(testDispatcher + broadcastFrameClock) {
        moleculeFlow(RecompositionMode.ContextClock) {
            start.periodUntil(
                clock = clock,
                unit = DateTimeUnit.SECOND,
            )
        }
            .distinctUntilChanged()
            .test {
                assertEquals(DateTimePeriod(), awaitItem())
                assertEquals(2, nowInvokedCount)

                advanceTimeBy(500.milliseconds)
                runCurrent()
                broadcastFrameClock.sendFrame((now - start).inWholeNanoseconds)

                expectNoEvents()
                assertEquals(2, nowInvokedCount)

                advanceTimeBy(500.milliseconds)
                runCurrent()
                broadcastFrameClock.sendFrame((now - start).inWholeNanoseconds)

                assertEquals(DateTimePeriod(seconds = 1), awaitItem())
                assertEquals(4, nowInvokedCount)
            }
    }

    @Test
    fun progressive_period_until_time_based() = runTest(testDispatcher + broadcastFrameClock) {
        advanceTimeBy(58.seconds)

        moleculeFlow(RecompositionMode.ContextClock) {
            start.progressivePeriodUntil(
                clock = clock,
                unitProgression = listOf(DateTimeUnit.HOUR, DateTimeUnit.MINUTE, DateTimeUnit.SECOND),
            )
        }
            .distinctUntilChanged()
            .test {
                assertEquals(DateTimeUnit.SECOND to DateTimePeriod(seconds = 58), awaitItem())
                assertEquals(2, nowInvokedCount)

                advanceTimeBy(500.milliseconds)
                runCurrent()
                broadcastFrameClock.sendFrame((now - start).inWholeNanoseconds)

                expectNoEvents()
                assertEquals(2, nowInvokedCount)

                advanceTimeBy(500.milliseconds)
                runCurrent()
                broadcastFrameClock.sendFrame((now - start).inWholeNanoseconds)

                assertEquals(DateTimeUnit.SECOND to DateTimePeriod(seconds = 59), awaitItem())
                assertEquals(4, nowInvokedCount)

                advanceTimeBy(500.milliseconds)
                runCurrent()
                broadcastFrameClock.sendFrame((now - start).inWholeNanoseconds)

                expectNoEvents()
                assertEquals(4, nowInvokedCount)

                advanceTimeBy(500.milliseconds)
                runCurrent()
                broadcastFrameClock.sendFrame((now - start).inWholeNanoseconds)

                assertEquals(DateTimeUnit.MINUTE to DateTimePeriod(seconds = 60), awaitItem())
                assertEquals(6, nowInvokedCount)

                advanceTimeBy(500.milliseconds)
                runCurrent()
                broadcastFrameClock.sendFrame((now - start).inWholeNanoseconds)

                expectNoEvents()
                assertEquals(6, nowInvokedCount)

                advanceTimeBy(500.milliseconds)
                runCurrent()
                broadcastFrameClock.sendFrame((now - start).inWholeNanoseconds)

                expectNoEvents()
                assertEquals(6, nowInvokedCount)

                advanceTimeBy(58.seconds)
                runCurrent()
                broadcastFrameClock.sendFrame((now - start).inWholeNanoseconds)

                expectNoEvents()
                assertEquals(6, nowInvokedCount)

                advanceTimeBy(1.seconds)
                runCurrent()
                broadcastFrameClock.sendFrame((now - start).inWholeNanoseconds)

                assertEquals(DateTimeUnit.MINUTE to DateTimePeriod(seconds = 120), awaitItem())
                assertEquals(8, nowInvokedCount)

                advanceTimeBy(58.minutes)
                runCurrent()
                broadcastFrameClock.sendFrame((now - start).inWholeNanoseconds)

                assertEquals(DateTimeUnit.HOUR to DateTimePeriod(seconds = 3600), awaitItem())
                assertEquals(10, nowInvokedCount)
            }
    }
}
