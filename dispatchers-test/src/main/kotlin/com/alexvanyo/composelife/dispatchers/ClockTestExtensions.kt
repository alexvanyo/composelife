package com.alexvanyo.composelife.dispatchers

import androidx.compose.ui.test.MainTestClock
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.test.TestCoroutineScheduler
import kotlinx.coroutines.test.TestScope
import kotlinx.datetime.Clock
import kotlinx.datetime.Instant

/**
 * Returns a [Clock] that is synced with the [TestScope.schedulerClock] from this [TestScope].
 *
 * In other words, the returned [Instant] will always be [TestCoroutineScheduler.currentTime].
 */
@OptIn(ExperimentalCoroutinesApi::class)
val TestScope.schedulerClock
    get(): Clock = object : Clock {
        override fun now(): Instant = Instant.fromEpochMilliseconds(testScheduler.currentTime)
    }

/**
 * Returns a [Clock] that is synced with the [MainTestClock].
 *
 * In other words, the returned [Instant] will always be [MainTestClock.currentTime].
 */
val MainTestClock.dateTimeClock
    get(): Clock = object : Clock {
        override fun now(): Instant = Instant.fromEpochMilliseconds(currentTime)
    }
