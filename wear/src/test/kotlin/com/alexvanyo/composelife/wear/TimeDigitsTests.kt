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

import org.junit.jupiter.api.extension.ExtensionContext
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.Arguments
import org.junit.jupiter.params.provider.ArgumentsProvider
import org.junit.jupiter.params.provider.ArgumentsSource
import java.time.LocalTime
import java.time.format.DateTimeFormatter
import java.util.Locale
import java.util.stream.Stream
import kotlin.test.assertEquals

class TimeDigitsTests {

    class TimeDigitsTestArguments(
        val expectedTimeDigits: TimeDigits,
        val localTime: LocalTime,
        val use24HourFormat: Boolean,
    ) {
        override fun toString(): String = "localTime: $localTime, use24HourFormat: $use24HourFormat"
    }

    class TimeDigitsTestProvider : ArgumentsProvider {
        override fun provideArguments(context: ExtensionContext?): Stream<out Arguments> =
            (0..23).flatMap { hour ->
                (0..59).map { minute ->
                    LocalTime.of(hour, minute)
                }
            }
                .flatMap { localTime ->
                    listOf(false, true).map { use24HourFormat ->
                        val ascendingOrderTime = localTime.format(
                            DateTimeFormatter.ofPattern(
                                if (use24HourFormat) "HHmm" else "hmm",
                                Locale.ROOT
                            )
                        )
                            .map { it.digitToInt().let(GameOfLifeSegmentChar.Companion::fromChar) }
                            .reversed()

                        val expectedTimeDigits = TimeDigits(
                            firstDigit = ascendingOrderTime.getOrElse(3) { GameOfLifeSegmentChar.Blank },
                            secondDigit = ascendingOrderTime.getOrElse(2) { GameOfLifeSegmentChar.Blank },
                            thirdDigit = ascendingOrderTime.getOrElse(1) { GameOfLifeSegmentChar.Blank },
                            fourthDigit = ascendingOrderTime.getOrElse(0) { GameOfLifeSegmentChar.Blank },
                        )

                        TimeDigitsTestArguments(
                            expectedTimeDigits = expectedTimeDigits,
                            localTime = localTime,
                            use24HourFormat = use24HourFormat
                        )
                    }
                }
                .stream()
                .map(Arguments::of)
    }

    @ParameterizedTest(name = "{displayName}: {0}")
    @ArgumentsSource(TimeDigitsTestProvider::class)
    fun `time digits are correct`(args: TimeDigitsTestArguments) {
        assertEquals(
            args.expectedTimeDigits,
            createTimeDigits(args.localTime, args.use24HourFormat)
        )
    }
}
