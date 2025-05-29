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

package com.alexvanyo.composelife.data

import androidx.work.ListenableWorker
import androidx.work.PeriodicWorkRequest
import androidx.work.PeriodicWorkRequestBuilder
import kotlinx.datetime.DateTimePeriod
import java.util.concurrent.TimeUnit
import kotlin.time.Duration.Companion.days
import kotlin.time.Duration.Companion.hours
import kotlin.time.Duration.Companion.minutes
import kotlin.time.Duration.Companion.nanoseconds
import kotlin.time.Duration.Companion.seconds

inline fun <reified T : ListenableWorker> PeriodicWorkRequestBuilder(
    repeatPeriod: DateTimePeriod,
): PeriodicWorkRequest.Builder =
    PeriodicWorkRequestBuilder<T>(
        repeatInterval = (repeatPeriod.nanoseconds.nanoseconds +
            repeatPeriod.seconds.seconds +
            repeatPeriod.minutes.minutes +
            repeatPeriod.hours.hours +
            repeatPeriod.days.days +
            ((repeatPeriod.months / 12.0 + repeatPeriod.years) * 365.2422).days).inWholeMilliseconds,
        repeatIntervalTimeUnit = TimeUnit.MILLISECONDS,
    )
