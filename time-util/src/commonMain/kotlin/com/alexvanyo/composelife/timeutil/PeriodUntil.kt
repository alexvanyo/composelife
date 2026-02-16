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

import androidx.compose.runtime.Composable
import androidx.compose.runtime.key
import androidx.compose.runtime.produceState
import androidx.compose.runtime.remember
import kotlinx.coroutines.delay
import kotlinx.coroutines.isActive
import kotlinx.datetime.DateTimePeriod
import kotlinx.datetime.DateTimeUnit
import kotlinx.datetime.TimeZone
import kotlinx.datetime.plus
import kotlinx.datetime.until
import kotlin.math.abs
import kotlin.time.Clock
import kotlin.time.Duration
import kotlin.time.Duration.Companion.days
import kotlin.time.Duration.Companion.hours
import kotlin.time.Duration.Companion.minutes
import kotlin.time.Duration.Companion.nanoseconds
import kotlin.time.Duration.Companion.seconds
import kotlin.time.Instant

/**
 * Returns an observable [DateTimePeriod] of [unit]s since the given [Instant], using the [clock] to determine the
 * current time.
 *
 * As time passes, this will return an updated [DateTimePeriod] automatically delaying the amount of time until the
 * [unit] will next change.
 */
@Suppress("ComposeUnstableReceiver")
@Composable
fun Instant.periodUntil(
    clock: Clock,
    unit: DateTimeUnit,
    timeZone: TimeZone,
): DateTimePeriod = key(this, clock, unit, timeZone) {
    produceState(
        remember {
            this.periodUntilWithUnit(
                other = clock.now(),
                unit = unit,
                timeZone = timeZone,
            )
        },
    ) {
        while (isActive) {
            val targetPeriod = when (unit) {
                is DateTimeUnit.TimeBased ->
                    DateTimePeriod(nanoseconds = value.totalNanoseconds + unit.nanoseconds)
                is DateTimeUnit.DayBased ->
                    DateTimePeriod(days = value.days + unit.days)
                is DateTimeUnit.MonthBased ->
                    DateTimePeriod(months = value.months + unit.months)
            }
            val targetInstant = this@periodUntil.plus(targetPeriod, timeZone)
            delay(targetInstant - clock.now())
            value = this@periodUntil.periodUntilWithUnit(
                other = clock.now(),
                unit = unit,
                timeZone = timeZone,
            )
        }
    }.value
}

/**
 * Returns an observable [DateTimePeriod] of [unit]s since the given [Instant], using the [clock] to determine the
 * current time.
 *
 * As time passes, this will return an updated [DateTimePeriod] automatically delaying the amount of time until the
 * [unit] will next change.
 */
@Suppress("ComposeUnstableReceiver")
@Composable
fun Instant.periodUntil(
    clock: Clock,
    unit: DateTimeUnit.TimeBased,
): DateTimePeriod = key(this, clock, unit) {
    produceState(
        remember {
            this.periodUntilWithUnit(
                other = clock.now(),
                unit = unit,
            )
        },
    ) {
        while (isActive) {
            val targetInstant = this@periodUntil.plus(
                value.timeComponentDuration + unit.duration,
            )
            delay(targetInstant - clock.now())
            value = this@periodUntil.periodUntilWithUnit(
                other = clock.now(),
                unit = unit,
            )
        }
    }.value
}

/**
 * Returns an observable [DateTimePeriod] for a progression of units since the given [Instant], using the [clock] to
 * determine the current time.
 *
 * The [unitProgression] should be sorted from "largest" unit to "smallest" unit, as the returned [DateTimeUnit]
 * will be the first one in the list such that the [DateTimePeriod] of that unit is non-zero. If the period for all
 * units is zero (which could be possible if the given [Instant] is the same or very close to the same as the current
 * time of the [clock]), then the last unit will be returned, with a [DateTimePeriod] that is zero in that unit.
 *
 * As time passes, this will return an updated [DateTimePeriod] automatically delaying the amount of time until the
 * returned pair would be different - either because the period would change, or the unit would change.
 */
@Suppress("ComposeUnstableReceiver")
@Composable
fun Instant.progressivePeriodUntil(
    clock: Clock,
    unitProgression: List<DateTimeUnit>,
    timeZone: TimeZone,
): Pair<DateTimeUnit, DateTimePeriod> =
    key(this, clock, unitProgression, timeZone) {
        produceState(
            remember {
                this.periodUntilWithProgressiveUnits(
                    other = clock.now(),
                    unitProgression = unitProgression,
                    timeZone = timeZone,
                )
            },
        ) {
            while (isActive) {
                // Determine the minimum (that is, the soonest to occur) instant where the period would change by
                // the given unit among the units that could be used as more time passes
                val unitIndex = unitProgression.indexOf(value.first)
                val targetInstant = unitProgression.subList(0, unitIndex + 1).minOf { unit ->
                    val period = when (unit) {
                        is DateTimeUnit.TimeBased ->
                            DateTimePeriod(nanoseconds = value.second.totalNanoseconds + unit.nanoseconds)
                        is DateTimeUnit.DayBased ->
                            DateTimePeriod(days = value.second.days + unit.days)
                        is DateTimeUnit.MonthBased ->
                            DateTimePeriod(months = value.second.months + unit.months)
                    }
                    this@progressivePeriodUntil.plus(period, timeZone)
                }
                delay(targetInstant - clock.now())
                value = this@progressivePeriodUntil.periodUntilWithProgressiveUnits(
                    other = clock.now(),
                    unitProgression = unitProgression,
                    timeZone = timeZone,
                )
            }
        }.value
    }

/**
 * Returns an observable [DateTimePeriod] for a progression of units since the given [Instant], using the [clock] to
 * determine the current time.
 *
 * The [unitProgression] should be sorted from "largest" unit to "smallest" unit, as the returned [DateTimeUnit]
 * will be the first one in the list such that the [DateTimePeriod] of that unit is non-zero. If the period for all
 * units is zero (which could be possible if the given [Instant] is the same or very close to the same as the current
 * time of the [clock]), then the last unit will be returned, with a [DateTimePeriod] that is zero in that unit.
 *
 * As time passes, this will return an updated [DateTimePeriod] automatically delaying the amount of time until the
 * returned pair would be different - either because the period would change, or the unit would change.
 */
@Suppress("ComposeUnstableReceiver")
@Composable
fun Instant.progressivePeriodUntil(
    clock: Clock,
    unitProgression: List<DateTimeUnit.TimeBased>,
): Pair<DateTimeUnit, DateTimePeriod> =
    key(this, clock, unitProgression) {
        produceState(
            remember {
                this.periodUntilWithProgressiveUnits(
                    other = clock.now(),
                    unitProgression = unitProgression,
                )
            },
        ) {
            while (isActive) {
                // Determine the minimum (that is, the soonest to occur) instant where the period would change by
                // the given unit among the units that could be used as more time passes
                val unitIndex = unitProgression.indexOf(value.first)
                val targetInstant = unitProgression.subList(0, unitIndex + 1).minOf { unit ->
                    this@progressivePeriodUntil.plus(
                        value.second.timeComponentDuration + unit.duration,
                    )
                }
                delay(targetInstant - clock.now())
                value = this@progressivePeriodUntil.periodUntilWithProgressiveUnits(
                    other = clock.now(),
                    unitProgression = unitProgression,
                )
            }
        }.value
    }

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

/**
 * Returns the approximate duration of the date component of the [DateTimePeriod] as a [Duration], where 1 year is
 * treated as equivalent to 365.2422 days, and 1 month is 1/12th of a year.
 */
val DateTimePeriod.dateComponentApproximateDuration: Duration get() =
    (days.days + ((months / 12.0 + years) * 365.2422).days).inWholeNanoseconds.nanoseconds

/**
 * Returns the total apprimxation duration of both the time component and date component of this [DateTimePeriod].
 */
val DateTimePeriod.approximateDuration: Duration get() = timeComponentDuration + dateComponentApproximateDuration
