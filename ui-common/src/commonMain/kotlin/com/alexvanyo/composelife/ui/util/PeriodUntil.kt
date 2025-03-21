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
import kotlinx.datetime.Instant
import kotlinx.datetime.TimeZone
import kotlinx.datetime.until
import kotlin.math.abs
import kotlin.time.Duration
import kotlin.time.Duration.Companion.hours
import kotlin.time.Duration.Companion.minutes
import kotlin.time.Duration.Companion.nanoseconds
import kotlin.time.Duration.Companion.seconds

/**
 * Returns the [DateTimePeriod] until the given [Instant] using the given [unit] in the given [timeZone].
 * The result will be a [DateTimePeriod] that is a whole number of [unit]s.
 */
internal fun Instant.periodUntilWithUnit(
    other: Instant,
    unit: DateTimeUnit,
    timeZone: TimeZone,
): DateTimePeriod {
    val value = until(other, unit, timeZone)
    return when (unit) {
        is DateTimeUnit.TimeBased -> DateTimePeriod(nanoseconds = unit.nanoseconds * value)
        is DateTimeUnit.DayBased -> DateTimePeriod(days = (unit.days * value).toInt())
        is DateTimeUnit.MonthBased -> DateTimePeriod(months = (unit.months * value).toInt())
    }
}

/**
 * Returns the [DateTimePeriod] until the given [Instant] using the given [unit].
 * The result will be a [DateTimePeriod] that is a whole number of [unit]s.
 */
internal fun Instant.periodUntilWithUnit(
    other: Instant,
    unit: DateTimeUnit.TimeBased,
): DateTimePeriod =
    DateTimePeriod(nanoseconds = unit.nanoseconds * until(other, unit))

/**
 * Returns the [DateTimePeriod] until the given [Instant] using the given [unitProgression]s in the given [timeZone].
 * The calculation is progressive, such that the unit used will be the first unit in the list (if any) where the
 * resulting [DateTimePeriod] is a whole, non-zero number of the unit.
 *
 * The return value is the pair of the chosen unit, and the resulting [DateTimePeriod] that is a multiple of that unit.
 *
 * If the period for all units is zero (which could be possible if [other] is the same or very close to [this]), then
 * the last unit will be returned, with a [DateTimePeriod] that is zero in that unit.
 */
internal fun Instant.periodUntilWithProgressiveUnits(
    other: Instant,
    unitProgression: List<DateTimeUnit>,
    timeZone: TimeZone,
): Pair<DateTimeUnit, DateTimePeriod> {
    val periods = unitProgression
        .map { unit ->
            unit to periodUntilWithUnit(other, unit, timeZone)
        }

    return periods.firstOrNull { (unit, period) ->
        when (unit) {
            is DateTimeUnit.TimeBased -> abs(period.timeComponentInWholeUnits(unit)) > 0
            is DateTimeUnit.DateBased -> abs(period.dateComponentInWholeUnits(unit)) > 0
        }
    } ?: periods.last()
}

/**
 * Returns the [DateTimePeriod] until the given [Instant] using the given [unitProgression]s.
 * The calculation is progressive, such that the unit used will be the first unit in the list (if any) where the
 * resulting [DateTimePeriod] is a whole, non-zero number of the unit.
 *
 * The return value is the pair of the chosen unit, and the resulting [DateTimePeriod] that is a multiple of that unit.
 *
 * If the period for all units is zero (which could be possible if [other] is the same or very close to [this]), then
 * the last unit will be returned, with a [DateTimePeriod] that is zero in that unit.
 */
internal fun Instant.periodUntilWithProgressiveUnits(
    other: Instant,
    unitProgression: List<DateTimeUnit.TimeBased>,
): Pair<DateTimeUnit.TimeBased, DateTimePeriod> {
    val periods = unitProgression
        .map { unit ->
            unit to periodUntilWithUnit(other, unit)
        }

    return periods.firstOrNull { (unit, period) ->
        abs(period.timeComponentInWholeUnits(unit)) > 0
    } ?: periods.last()
}

/**
 * Returns the whole number of [unit]s in the date component of the [DateTimePeriod]. The result is truncated toward
 * zero.
 */
fun DateTimePeriod.dateComponentInWholeUnits(unit: DateTimeUnit.DateBased): Int =
    when (unit) {
        is DateTimeUnit.DayBased -> days / unit.days
        is DateTimeUnit.MonthBased -> months / unit.months
    }

/**
 * Returns the whole number of [unit]s in the time component of the [DateTimePeriod]. The result is truncated toward
 * zero.
 */
fun DateTimePeriod.timeComponentInWholeUnits(unit: DateTimeUnit.TimeBased): Long =
    totalNanoseconds / unit.nanoseconds

/**
 * Returns the total number of nanoseconds of the time component of the [DateTimePeriod].
 */
val DateTimePeriod.totalNanoseconds: Long get() =
    nanoseconds +
        seconds.seconds.inWholeNanoseconds +
        minutes.minutes.inWholeNanoseconds +
        hours.hours.inWholeNanoseconds

/**
 * Returns the time component of the [DateTimePeriod] as a [Duration].
 */
val DateTimePeriod.timeComponentDuration: Duration get() =
    totalNanoseconds.nanoseconds
