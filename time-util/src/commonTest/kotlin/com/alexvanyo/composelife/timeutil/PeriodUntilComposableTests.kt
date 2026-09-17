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

package com.alexvanyo.composelife.timeutil

import androidx.appstate.transform.transform
import androidx.compose.runtime.snapshots.Snapshot
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.test.StandardTestDispatcher
import kotlinx.coroutines.test.TestCoroutineScheduler
import kotlinx.coroutines.test.runCurrent
import kotlinx.coroutines.test.runTest
import kotlinx.datetime.DateTimePeriod
import kotlinx.datetime.DateTimeUnit
import kotlinx.datetime.TimeZone
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.time.Clock
import kotlin.time.Duration
import kotlin.time.Duration.Companion.days
import kotlin.time.Duration.Companion.hours
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
    private var nowInvokedCount = 0

    private val clock = object : Clock {
        override fun now(): Instant = now.also { nowInvokedCount++ }
    }

    private fun advanceTimeBy(duration: Duration) {
        now += duration
        testScheduler.advanceTimeBy(duration)
        testScheduler.runCurrent()
        Snapshot.sendApplyNotifications()
        testScheduler.runCurrent()
    }

    @Test
    fun period_until_time_based() = runTest(testDispatcher) {
        val state = transform(
            initialValue = DateTimePeriod(),
            scope = backgroundScope,
            dispatcher = testDispatcher,
        ) {
            start.periodUntil(
                clock = clock,
                unit = DateTimeUnit.SECOND,
            )
        }
        runCurrent()

        assertEquals(DateTimePeriod(), state.value)
        assertEquals(2, nowInvokedCount)

        advanceTimeBy(500.milliseconds)
        runCurrent()

        assertEquals(DateTimePeriod(), state.value)
        assertEquals(2, nowInvokedCount)

        advanceTimeBy(500.milliseconds)
        runCurrent()

        assertEquals(DateTimePeriod(seconds = 1), state.value)
        assertEquals(4, nowInvokedCount)
    }

    @Test
    fun progressive_period_until_time_based() = runTest(testDispatcher) {
        advanceTimeBy(58.seconds)

        val state = transform<Pair<DateTimeUnit, DateTimePeriod>>(
            initialValue = DateTimeUnit.SECOND to DateTimePeriod(seconds = 58),
            scope = backgroundScope,
            dispatcher = testDispatcher,
        ) {
            start.progressivePeriodUntil(
                clock = clock,
                unitProgression = listOf(DateTimeUnit.HOUR, DateTimeUnit.MINUTE, DateTimeUnit.SECOND),
            )
        }
        runCurrent()

        assertEquals(DateTimeUnit.SECOND to DateTimePeriod(seconds = 58), state.value)
        assertEquals(2, nowInvokedCount)

        advanceTimeBy(500.milliseconds)
        runCurrent()

        assertEquals(DateTimeUnit.SECOND to DateTimePeriod(seconds = 58), state.value)
        assertEquals(2, nowInvokedCount)

        advanceTimeBy(500.milliseconds)
        runCurrent()

        assertEquals(DateTimeUnit.SECOND to DateTimePeriod(seconds = 59), state.value)
        assertEquals(4, nowInvokedCount)

        advanceTimeBy(500.milliseconds)
        runCurrent()

        assertEquals(DateTimeUnit.SECOND to DateTimePeriod(seconds = 59), state.value)
        assertEquals(4, nowInvokedCount)

        advanceTimeBy(500.milliseconds)
        runCurrent()

        assertEquals(DateTimeUnit.MINUTE to DateTimePeriod(seconds = 60), state.value)
        assertEquals(6, nowInvokedCount)

        advanceTimeBy(500.milliseconds)
        runCurrent()

        assertEquals(DateTimeUnit.MINUTE to DateTimePeriod(seconds = 60), state.value)
        assertEquals(6, nowInvokedCount)

        advanceTimeBy(500.milliseconds)
        runCurrent()

        assertEquals(DateTimeUnit.MINUTE to DateTimePeriod(seconds = 60), state.value)
        assertEquals(6, nowInvokedCount)

        advanceTimeBy(58.seconds)
        runCurrent()

        assertEquals(DateTimeUnit.MINUTE to DateTimePeriod(seconds = 60), state.value)
        assertEquals(6, nowInvokedCount)

        advanceTimeBy(1.seconds)
        runCurrent()

        assertEquals(DateTimeUnit.MINUTE to DateTimePeriod(seconds = 120), state.value)
        assertEquals(8, nowInvokedCount)

        advanceTimeBy(58.minutes)
        runCurrent()

        assertEquals(DateTimeUnit.HOUR to DateTimePeriod(seconds = 3600), state.value)
        assertEquals(10, nowInvokedCount)
    }

    @Test
    fun period_until_time_based_with_time_zone() = runTest(testDispatcher) {
        val state = transform(
            initialValue = DateTimePeriod(),
            scope = backgroundScope,
            dispatcher = testDispatcher,
        ) {
            start.periodUntil(
                clock = clock,
                unit = DateTimeUnit.SECOND,
                timeZone = TimeZone.UTC,
            )
        }
        runCurrent()

        assertEquals(DateTimePeriod(), state.value)
        assertEquals(2, nowInvokedCount)

        advanceTimeBy(500.milliseconds)
        runCurrent()

        assertEquals(DateTimePeriod(), state.value)
        assertEquals(2, nowInvokedCount)

        advanceTimeBy(500.milliseconds)
        runCurrent()

        assertEquals(DateTimePeriod(seconds = 1), state.value)
        assertEquals(4, nowInvokedCount)
    }

    @Test
    fun period_until_day_based() = runTest(testDispatcher) {
        val state = transform(
            initialValue = DateTimePeriod(),
            scope = backgroundScope,
            dispatcher = testDispatcher,
        ) {
            start.periodUntil(
                clock = clock,
                unit = DateTimeUnit.DAY,
                timeZone = TimeZone.UTC,
            )
        }

        assertEquals(DateTimePeriod(), state.value)

        advanceTimeBy(12.hours)
        runCurrent()
        assertEquals(DateTimePeriod(), state.value)

        advanceTimeBy(12.hours)
        runCurrent()
        assertEquals(DateTimePeriod(days = 1), state.value)
    }

    @Test
    fun period_until_month_based() = runTest(testDispatcher) {
        val state = transform(
            initialValue = DateTimePeriod(),
            scope = backgroundScope,
            dispatcher = testDispatcher,
        ) {
            start.periodUntil(
                clock = clock,
                unit = DateTimeUnit.MONTH,
                timeZone = TimeZone.UTC,
            )
        }

        assertEquals(DateTimePeriod(), state.value)

        advanceTimeBy(15.days)
        runCurrent()
        assertEquals(DateTimePeriod(), state.value)

        advanceTimeBy(16.days)
        runCurrent()
        assertEquals(DateTimePeriod(months = 1), state.value)
    }

    @Test
    fun progressive_period_until_with_date_units() = runTest(testDispatcher) {
        val state = transform<Pair<DateTimeUnit, DateTimePeriod>>(
            initialValue = DateTimeUnit.HOUR to DateTimePeriod(),
            scope = backgroundScope,
            dispatcher = testDispatcher,
        ) {
            start.progressivePeriodUntil(
                clock = clock,
                unitProgression = listOf(DateTimeUnit.MONTH, DateTimeUnit.DAY, DateTimeUnit.HOUR),
                timeZone = TimeZone.UTC,
            )
        }

        assertEquals(DateTimeUnit.HOUR to DateTimePeriod(), state.value)

        advanceTimeBy(1.hours)
        runCurrent()
        assertEquals(DateTimeUnit.HOUR to DateTimePeriod(hours = 1), state.value)

        advanceTimeBy(23.hours)
        runCurrent()
        assertEquals(DateTimeUnit.DAY to DateTimePeriod(days = 1), state.value)

        advanceTimeBy(31.days)
        runCurrent()
        assertEquals(DateTimeUnit.MONTH to DateTimePeriod(months = 1), state.value)
    }
}
