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
@file:Suppress("MatchingDeclarationName")

package com.alexvanyo.composelife.ui.settings

import androidx.compose.foundation.text.input.InputTransformation
import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.remember
import androidx.compose.ui.Modifier
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResolver
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResource
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.di.LoadedComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.setPatternCollectionsSynchronizationPeriod
import com.alexvanyo.composelife.sessionvalue.SessionValue
import com.alexvanyo.composelife.sessionvalue.map
import com.alexvanyo.composelife.ui.mobile.component.EditableSlider
import com.alexvanyo.composelife.ui.mobile.component.SliderBijection
import com.alexvanyo.composelife.ui.settings.resources.PatternCollectionsSynchronizationPeriod
import com.alexvanyo.composelife.ui.settings.resources.PatternCollectionsSynchronizationPeriodLabelAndValue
import com.alexvanyo.composelife.ui.settings.resources.PatternCollectionsSynchronizationPeriodValue
import com.alexvanyo.composelife.ui.settings.resources.Strings
import com.alexvanyo.composelife.ui.util.nonNegativeDouble
import kotlinx.coroutines.channels.Channel
import kotlinx.datetime.DateTimePeriod
import kotlin.math.log2
import kotlin.math.pow
import kotlin.math.roundToInt
import kotlin.time.Duration.Companion.days
import kotlin.time.Duration.Companion.hours
import kotlin.time.Duration.Companion.minutes
import kotlin.time.Duration.Companion.nanoseconds
import kotlin.time.Duration.Companion.seconds

interface PatternCollectionsSynchronizationPeriodUiInjectEntryPoint :
    ComposeLifePreferencesProvider

interface PatternCollectionsSynchronizationPeriodUiLocalEntryPoint :
    LoadedComposeLifePreferencesProvider

context(
    injectEntryPoint: PatternCollectionsSynchronizationPeriodUiInjectEntryPoint,
    localEntryPoint: PatternCollectionsSynchronizationPeriodUiLocalEntryPoint
)
@Composable
fun PatternCollectionsSynchronizationPeriodUi(
    modifier: Modifier = Modifier,
) {
    PatternCollectionsSynchronizationPeriodUi(
        patternCollectionsSynchronizationPeriodSessionValue =
            localEntryPoint.preferences.patternCollectionsSynchronizationPeriodSessionValue,
        setPatternCollectionsSynchronizationPeriodSessionValue =
            injectEntryPoint.composeLifePreferences::setPatternCollectionsSynchronizationPeriod,
        modifier = modifier,
    )
}

@Composable
fun PatternCollectionsSynchronizationPeriodUi(
    patternCollectionsSynchronizationPeriodSessionValue: SessionValue<DateTimePeriod>,
    setPatternCollectionsSynchronizationPeriodSessionValue: suspend (expected: SessionValue<DateTimePeriod>, newValue: SessionValue<DateTimePeriod>) -> Unit,
    modifier: Modifier = Modifier,
) {
    val resolver = parameterizedStringResolver()

    val patternCollectionsSynchronizationPeriodUpdates = remember {
        Channel<Pair<SessionValue<DateTimePeriod>, SessionValue<DateTimePeriod>>>(
            capacity = Channel.UNLIMITED,
        )
    }

    LaunchedEffect(patternCollectionsSynchronizationPeriodUpdates, setPatternCollectionsSynchronizationPeriodSessionValue) {
        while (true) {
            val pendingUpdates = patternCollectionsSynchronizationPeriodUpdates.receiveBatch()
            setPatternCollectionsSynchronizationPeriodSessionValue(
                pendingUpdates.first().first,
                pendingUpdates.last().second,
            )
        }
    }

    EditableSlider(
        labelAndValueText = { parameterizedStringResource(Strings.PatternCollectionsSynchronizationPeriodLabelAndValue(it)) },
        valueText = { resolver(Strings.PatternCollectionsSynchronizationPeriodValue(it)) },
        labelText = parameterizedStringResource(Strings.PatternCollectionsSynchronizationPeriod),
        textToValue = { it.toFloatOrNull() },
        sessionValue = patternCollectionsSynchronizationPeriodSessionValue.map {
            (it.nanoseconds.nanoseconds +
                it.seconds.seconds +
                it.minutes.minutes +
                it.hours.hours +
                it.days.days +
                ((it.months / 12.0 + it.years) * 365.2422).days).inWholeMilliseconds /
                    1.minutes.inWholeMilliseconds.toFloat()
        },
        onSessionValueChange = { expected, newValue ->
            patternCollectionsSynchronizationPeriodUpdates.trySend(
                expected.map { DateTimePeriod(minutes = it.roundToInt()) } to
                        newValue.map { DateTimePeriod(minutes = it.roundToInt()) }
            )
        },
        modifier = modifier,
        valueRange = 15f..7.days.inWholeMinutes.toFloat(),
        sliderBijection = PatternCollectionsSynchronizationPeriodBijection,
        inputTransformation = InputTransformation.nonNegativeDouble(),
    )
}

private object PatternCollectionsSynchronizationPeriodBijection : SliderBijection<Float> {
    override fun valueToSlider(value: Float): Float = log2(value)
    override fun sliderToValue(sliderValue: Float): Float = 2.0f.pow(sliderValue)
}
