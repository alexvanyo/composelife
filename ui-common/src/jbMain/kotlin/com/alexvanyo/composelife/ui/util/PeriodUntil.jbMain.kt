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

import androidx.compose.runtime.Composable
import androidx.compose.runtime.key
import androidx.compose.runtime.produceState
import androidx.compose.runtime.remember
import kotlinx.coroutines.delay
import kotlinx.coroutines.isActive
import kotlinx.datetime.Clock
import kotlinx.datetime.DateTimePeriod
import kotlinx.datetime.DateTimeUnit
import kotlinx.datetime.Instant
import kotlinx.datetime.TimeZone
import kotlinx.datetime.plus

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
