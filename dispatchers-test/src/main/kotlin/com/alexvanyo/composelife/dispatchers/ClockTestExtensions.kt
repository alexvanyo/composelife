/*
 * Copyright 2022 The Android Open Source Project
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

package com.alexvanyo.composelife.dispatchers

import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.test.TestCoroutineScheduler
import kotlinx.coroutines.test.TestScope
import kotlinx.datetime.Clock
import kotlinx.datetime.Instant

/**
 * Returns a [Clock] that is synced with the [TestScope.schedulerClock] from this [TestScope].
 */
@OptIn(ExperimentalCoroutinesApi::class)
val TestScope.schedulerClock
    get(): Clock = testScheduler.clock

/**
 * Returns a [Clock] that is synced with this scheduler.
 *
 * In other words, the returned [Instant] will always be [TestCoroutineScheduler.currentTime].
 */
@OptIn(ExperimentalCoroutinesApi::class)
val TestCoroutineScheduler.clock
    get(): Clock = object : Clock {
        override fun now(): Instant = Instant.fromEpochMilliseconds(currentTime)
    }
