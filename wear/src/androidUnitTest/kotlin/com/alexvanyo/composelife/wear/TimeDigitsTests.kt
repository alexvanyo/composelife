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

package com.alexvanyo.composelife.wear

import com.google.testing.junit.testparameterinjector.TestParameter
import com.google.testing.junit.testparameterinjector.TestParameterInjector
import org.junit.runner.RunWith
import java.time.LocalTime
import java.time.format.DateTimeFormatter
import java.util.Locale
import kotlin.test.Test
import kotlin.test.assertEquals

@RunWith(TestParameterInjector::class)
class TimeDigitsTests {

    class LocalTimeProvider : TestParameter.TestParameterValuesProvider {
        override fun provideValues() =
            (0..23).flatMap { hour ->
                (0..59).map { minute ->
                    LocalTime.of(hour, minute)
                }
            }
    }

    @Test
    fun `time digits are correct`(
        @TestParameter(valuesProvider = LocalTimeProvider::class) localTime: LocalTime,
        @TestParameter use24HourFormat: Boolean,
    ) {
        val ascendingOrderTime = localTime.format(
            DateTimeFormatter.ofPattern(
                if (use24HourFormat) "HHmm" else "hmm",
                Locale.ROOT,
            ),
        )
            .map { it.digitToInt().let(GameOfLifeSegmentChar.Companion::fromChar) }
            .reversed()

        val expectedTimeDigits = TimeDigits(
            firstDigit = ascendingOrderTime.getOrElse(3) { GameOfLifeSegmentChar.Blank },
            secondDigit = ascendingOrderTime.getOrElse(2) { GameOfLifeSegmentChar.Blank },
            thirdDigit = ascendingOrderTime.getOrElse(1) { GameOfLifeSegmentChar.Blank },
            fourthDigit = ascendingOrderTime.getOrElse(0) { GameOfLifeSegmentChar.Blank },
        )

        assertEquals(
            expectedTimeDigits,
            createTimeDigits(localTime, use24HourFormat),
        )
    }
}
