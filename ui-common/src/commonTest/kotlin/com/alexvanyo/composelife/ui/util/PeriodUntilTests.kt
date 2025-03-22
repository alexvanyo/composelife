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

import kotlinx.datetime.DateTimePeriod
import kotlinx.datetime.DateTimeUnit
import kotlinx.datetime.TimeZone
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.time.Duration.Companion.days
import kotlin.time.Duration.Companion.hours
import kotlin.time.Duration.Companion.minutes
import kotlin.time.Duration.Companion.nanoseconds
import kotlin.time.Duration.Companion.seconds
import kotlin.time.Instant

class PeriodUntilTests {

    @Test
    fun periodUntilWithUnit_time_based_second_positive() {
        val start = Instant.fromEpochMilliseconds(1741463473365L)
        val end = start + 63.seconds

        val result = start.periodUntilWithUnit(end, DateTimeUnit.SECOND)

        assertEquals(DateTimePeriod(minutes = 1, seconds = 3), result)
    }

    @Test
    fun periodUntilWithUnit_time_based_second_negative() {
        val start = Instant.fromEpochMilliseconds(1741463473365L)
        val end = start - 63.seconds

        val result = start.periodUntilWithUnit(end, DateTimeUnit.SECOND)

        assertEquals(DateTimePeriod(minutes = -1, seconds = -3), result)
    }

    @Test
    fun periodUntilWithUnit_time_based_minute_positive() {
        val start = Instant.fromEpochMilliseconds(1741463473365L)
        val end = start + 131.minutes

        val result = start.periodUntilWithUnit(end, DateTimeUnit.MINUTE)

        assertEquals(DateTimePeriod(hours = 2, minutes = 11), result)
    }

    @Test
    fun periodUntilWithUnit_time_based_minute_negative() {
        val start = Instant.fromEpochMilliseconds(1741463473365L)
        val end = start - 131.minutes

        val result = start.periodUntilWithUnit(end, DateTimeUnit.MINUTE)

        assertEquals(DateTimePeriod(hours = -2, minutes = -11), result)
    }

    @Test
    fun periodUntilWithUnit_time_based_hour_positive() {
        val start = Instant.fromEpochMilliseconds(1741463473365L)
        val end = start + 131.minutes

        val result = start.periodUntilWithUnit(end, DateTimeUnit.HOUR)

        assertEquals(DateTimePeriod(hours = 2), result)
    }

    @Test
    fun periodUntilWithUnit_time_based_hour_negative() {
        val start = Instant.fromEpochMilliseconds(1741463473365L)
        val end = start - 131.minutes

        val result = start.periodUntilWithUnit(end, DateTimeUnit.HOUR)

        assertEquals(DateTimePeriod(hours = -2), result)
    }

    @Test
    fun periodUntilWithUnit_date_based_hour_positive() {
        val start = Instant.fromEpochMilliseconds(1741463473365L)
        val end = start + 1.hours

        val result = start.periodUntilWithUnit(end, DateTimeUnit.HOUR, TimeZone.UTC)

        assertEquals(DateTimePeriod(hours = 1), result)
    }

    @Test
    fun periodUntilWithUnit_date_based_hour_negative() {
        val start = Instant.fromEpochMilliseconds(1741463473365L)
        val end = start - 1.hours

        val result = start.periodUntilWithUnit(end, DateTimeUnit.HOUR, TimeZone.UTC)

        assertEquals(DateTimePeriod(hours = -1), result)
    }

    @Test
    fun periodUntilWithUnit_date_based_day_positive() {
        val start = Instant.fromEpochMilliseconds(1741463473365L)
        val end = start + 1.days

        val result = start.periodUntilWithUnit(end, DateTimeUnit.DAY, TimeZone.UTC)

        assertEquals(DateTimePeriod(days = 1), result)
    }

    @Test
    fun periodUntilWithUnit_date_based_day_negative() {
        val start = Instant.fromEpochMilliseconds(1741463473365L)
        val end = start - 1.days

        val result = start.periodUntilWithUnit(end, DateTimeUnit.DAY, TimeZone.UTC)

        assertEquals(DateTimePeriod(days = -1), result)
    }

    @Test
    fun periodUntilWithUnit_date_based_month_positive() {
        val start = Instant.fromEpochMilliseconds(1741463473365L)
        val end = start + 31.days

        val result = start.periodUntilWithUnit(end, DateTimeUnit.MONTH, TimeZone.UTC)

        assertEquals(DateTimePeriod(months = 1), result)
    }

    @Test
    fun periodUntilWithUnit_date_based_month_negative() {
        val start = Instant.fromEpochMilliseconds(1741463473365L)
        val end = start - 31.days

        val result = start.periodUntilWithUnit(end, DateTimeUnit.MONTH, TimeZone.UTC)

        assertEquals(DateTimePeriod(months = -1), result)
    }

    @Test
    fun periodUntilWithProgressiveUnits_date_based_hour_positive() {
        val start = Instant.fromEpochMilliseconds(1741463473365L)
        val end = start + 131.minutes

        val result = start.periodUntilWithProgressiveUnits(
            other = end,
            unitProgression = listOf(DateTimeUnit.HOUR, DateTimeUnit.MINUTE, DateTimeUnit.SECOND),
            timeZone = TimeZone.UTC,
        )

        assertEquals(DateTimeUnit.HOUR to DateTimePeriod(hours = 2), result)
    }

    @Test
    fun periodUntilWithProgressiveUnits_date_based_hour_negative() {
        val start = Instant.fromEpochMilliseconds(1741463473365L)
        val end = start - 131.minutes

        val result = start.periodUntilWithProgressiveUnits(
            other = end,
            unitProgression = listOf(DateTimeUnit.HOUR, DateTimeUnit.MINUTE, DateTimeUnit.SECOND),
            timeZone = TimeZone.UTC,
        )

        assertEquals(DateTimeUnit.HOUR to DateTimePeriod(hours = -2), result)
    }

    @Test
    fun periodUntilWithProgressiveUnits_date_based_minute_positive() {
        val start = Instant.fromEpochMilliseconds(1741463473365L)
        val end = start + 27.minutes

        val result = start.periodUntilWithProgressiveUnits(
            other = end,
            unitProgression = listOf(DateTimeUnit.HOUR, DateTimeUnit.MINUTE, DateTimeUnit.SECOND),
            timeZone = TimeZone.UTC,
        )

        assertEquals(DateTimeUnit.MINUTE to DateTimePeriod(minutes = 27), result)
    }

    @Test
    fun periodUntilWithProgressiveUnits_date_based_minute_negative() {
        val start = Instant.fromEpochMilliseconds(1741463473365L)
        val end = start - 27.minutes

        val result = start.periodUntilWithProgressiveUnits(
            other = end,
            unitProgression = listOf(DateTimeUnit.HOUR, DateTimeUnit.MINUTE, DateTimeUnit.SECOND),
            timeZone = TimeZone.UTC,
        )

        assertEquals(DateTimeUnit.MINUTE to DateTimePeriod(minutes = -27), result)
    }

    @Test
    fun periodUntilWithProgressiveUnits_date_based_seconds_positive() {
        val start = Instant.fromEpochMilliseconds(1741463473365L)
        val end = start + 45.seconds

        val result = start.periodUntilWithProgressiveUnits(
            other = end,
            unitProgression = listOf(DateTimeUnit.HOUR, DateTimeUnit.MINUTE, DateTimeUnit.SECOND),
            timeZone = TimeZone.UTC,
        )

        assertEquals(DateTimeUnit.SECOND to DateTimePeriod(seconds = 45), result)
    }

    @Test
    fun periodUntilWithProgressiveUnits_date_based_seconds_negative() {
        val start = Instant.fromEpochMilliseconds(1741463473365L)
        val end = start - 45.seconds

        val result = start.periodUntilWithProgressiveUnits(
            other = end,
            unitProgression = listOf(DateTimeUnit.HOUR, DateTimeUnit.MINUTE, DateTimeUnit.SECOND),
            timeZone = TimeZone.UTC,
        )

        assertEquals(DateTimeUnit.SECOND to DateTimePeriod(seconds = -45), result)
    }

    @Test
    fun periodUntilWithProgressiveUnits_date_based_same_instant() {
        val start = Instant.fromEpochMilliseconds(1741463473365L)
        val end = start

        val result = start.periodUntilWithProgressiveUnits(
            other = end,
            unitProgression = listOf(DateTimeUnit.HOUR, DateTimeUnit.MINUTE, DateTimeUnit.SECOND),
            timeZone = TimeZone.UTC,
        )

        assertEquals(DateTimeUnit.SECOND to DateTimePeriod(), result)
    }

    @Test
    fun periodUntilWithProgressiveUnits_time_based_hour_positive() {
        val start = Instant.fromEpochMilliseconds(1741463473365L)
        val end = start + 131.minutes

        val result = start.periodUntilWithProgressiveUnits(
            other = end,
            unitProgression = listOf(DateTimeUnit.HOUR, DateTimeUnit.MINUTE, DateTimeUnit.SECOND),
        )

        assertEquals(DateTimeUnit.HOUR to DateTimePeriod(hours = 2), result)
    }

    @Test
    fun periodUntilWithProgressiveUnits_time_based_hour_negative() {
        val start = Instant.fromEpochMilliseconds(1741463473365L)
        val end = start - 131.minutes

        val result = start.periodUntilWithProgressiveUnits(
            other = end,
            unitProgression = listOf(DateTimeUnit.HOUR, DateTimeUnit.MINUTE, DateTimeUnit.SECOND),
        )

        assertEquals(DateTimeUnit.HOUR to DateTimePeriod(hours = -2), result)
    }

    @Test
    fun periodUntilWithProgressiveUnits_time_based_minute_positive() {
        val start = Instant.fromEpochMilliseconds(1741463473365L)
        val end = start + 27.minutes

        val result = start.periodUntilWithProgressiveUnits(
            other = end,
            unitProgression = listOf(DateTimeUnit.HOUR, DateTimeUnit.MINUTE, DateTimeUnit.SECOND),
        )

        assertEquals(DateTimeUnit.MINUTE to DateTimePeriod(minutes = 27), result)
    }

    @Test
    fun periodUntilWithProgressiveUnits_time_based_minute_negative() {
        val start = Instant.fromEpochMilliseconds(1741463473365L)
        val end = start - 27.minutes

        val result = start.periodUntilWithProgressiveUnits(
            other = end,
            unitProgression = listOf(DateTimeUnit.HOUR, DateTimeUnit.MINUTE, DateTimeUnit.SECOND),
        )

        assertEquals(DateTimeUnit.MINUTE to DateTimePeriod(minutes = -27), result)
    }

    @Test
    fun periodUntilWithProgressiveUnits_time_based_seconds_positive() {
        val start = Instant.fromEpochMilliseconds(1741463473365L)
        val end = start + 45.seconds

        val result = start.periodUntilWithProgressiveUnits(
            other = end,
            unitProgression = listOf(DateTimeUnit.HOUR, DateTimeUnit.MINUTE, DateTimeUnit.SECOND),
        )

        assertEquals(DateTimeUnit.SECOND to DateTimePeriod(seconds = 45), result)
    }

    @Test
    fun periodUntilWithProgressiveUnits_time_based_seconds_negative() {
        val start = Instant.fromEpochMilliseconds(1741463473365L)
        val end = start - 45.seconds

        val result = start.periodUntilWithProgressiveUnits(
            other = end,
            unitProgression = listOf(DateTimeUnit.HOUR, DateTimeUnit.MINUTE, DateTimeUnit.SECOND),
        )

        assertEquals(DateTimeUnit.SECOND to DateTimePeriod(seconds = -45), result)
    }

    @Test
    fun periodUntilWithProgressiveUnits_time_based_same_instant() {
        val start = Instant.fromEpochMilliseconds(1741463473365L)
        val end = start

        val result = start.periodUntilWithProgressiveUnits(
            other = end,
            unitProgression = listOf(DateTimeUnit.HOUR, DateTimeUnit.MINUTE, DateTimeUnit.SECOND),
        )

        assertEquals(DateTimeUnit.SECOND to DateTimePeriod(), result)
    }

    @Test
    fun dateComponentInWholeUnits_day_based_positive() {
        val period = DateTimePeriod(days = 2)

        val result = period.dateComponentInWholeUnits(DateTimeUnit.DAY)

        assertEquals(2, result)
    }

    @Test
    fun dateComponentInWholeUnits_day_based_negative() {
        val period = DateTimePeriod(days = -2)

        val result = period.dateComponentInWholeUnits(DateTimeUnit.DAY)

        assertEquals(-2, result)
    }

    @Test
    fun dateComponentInWholeUnits_month_based_positive() {
        val period = DateTimePeriod(months = 2)

        val result = period.dateComponentInWholeUnits(DateTimeUnit.MONTH)

        assertEquals(2, result)
    }

    @Test
    fun dateComponentInWholeUnits_month_based_negative() {
        val period = DateTimePeriod(months = -2)

        val result = period.dateComponentInWholeUnits(DateTimeUnit.MONTH)

        assertEquals(-2, result)
    }

    @Test
    fun timeComponentInWholeUnits_nanosecond_based_positive() {
        val period = DateTimePeriod(nanoseconds = 2)

        val result = period.timeComponentInWholeUnits(DateTimeUnit.NANOSECOND)

        assertEquals(2, result)
    }

    @Test
    fun timeComponentInWholeUnits_nanosecond_based_negative() {
        val period = DateTimePeriod(nanoseconds = -2)

        val result = period.timeComponentInWholeUnits(DateTimeUnit.NANOSECOND)

        assertEquals(-2, result)
    }

    @Test
    fun timeComponentInWholeUnits_hour_based_positive() {
        val period = DateTimePeriod(hours = 2)

        val result = period.timeComponentInWholeUnits(DateTimeUnit.HOUR)

        assertEquals(2, result)
    }

    @Test
    fun timeComponentInWholeUnits_hour_based_negative() {
        val period = DateTimePeriod(hours = -2)

        val result = period.timeComponentInWholeUnits(DateTimeUnit.HOUR)

        assertEquals(-2, result)
    }

    @Test
    fun totalNanoseconds_nanosecond() {
        val period = DateTimePeriod(nanoseconds = 1)

        assertEquals(1.nanoseconds.inWholeNanoseconds, period.totalNanoseconds)
    }

    @Test
    fun totalNanoseconds_second() {
        val period = DateTimePeriod(seconds = 1)

        assertEquals(1.seconds.inWholeNanoseconds, period.totalNanoseconds)
    }

    @Test
    fun totalNanoseconds_minute() {
        val period = DateTimePeriod(minutes = 1)

        assertEquals(1.minutes.inWholeNanoseconds, period.totalNanoseconds)
    }

    @Test
    fun totalNanoseconds_hour() {
        val period = DateTimePeriod(hours = 1)

        assertEquals(1.hours.inWholeNanoseconds, period.totalNanoseconds)
    }
}
