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
@file:Suppress("MatchingDeclarationName")

package com.alexvanyo.composelife.ui.settings

import androidx.compose.foundation.text.input.InputTransformation
import androidx.compose.material3.Text
import androidx.compose.runtime.Composable
import androidx.compose.runtime.Immutable
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.mutableDoubleStateOf
import androidx.compose.runtime.mutableFloatStateOf
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.saveable.rememberSaveable
import androidx.compose.runtime.setValue
import androidx.compose.ui.Modifier
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResolver
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResource
import com.alexvanyo.composelife.preferences.ComposeLifePreferences
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferences
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferencesHolder
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.di.LoadedComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.setPatternCollectionsSynchronizationPeriod
import com.alexvanyo.composelife.serialization.uuidSaver
import com.alexvanyo.composelife.sessionvalue.SessionValue
import com.alexvanyo.composelife.sessionvalue.localSessionId
import com.alexvanyo.composelife.sessionvalue.map
import com.alexvanyo.composelife.sessionvalue.rememberAsyncSessionValueHolder
import com.alexvanyo.composelife.sessionvalue.rememberSessionValueHolder
import com.alexvanyo.composelife.ui.mobile.component.EditableSlider
import com.alexvanyo.composelife.ui.mobile.component.SliderBijection
import com.alexvanyo.composelife.ui.settings.resources.PatternCollectionsSynchronizationPeriod
import com.alexvanyo.composelife.ui.settings.resources.PatternCollectionsSynchronizationPeriodLabelAndValue
import com.alexvanyo.composelife.ui.settings.resources.PatternCollectionsSynchronizationPeriodSuffix
import com.alexvanyo.composelife.ui.settings.resources.PatternCollectionsSynchronizationPeriodValue
import com.alexvanyo.composelife.ui.settings.resources.Strings
import com.alexvanyo.composelife.ui.util.nonNegativeDouble
import dev.zacsweers.metro.Inject
import kotlinx.datetime.DateTimePeriod
import kotlinx.datetime.toDateTimePeriod
import kotlin.math.log2
import kotlin.math.pow
import kotlin.math.roundToInt
import kotlin.time.Duration.Companion.days
import kotlin.time.Duration.Companion.hours
import kotlin.time.Duration.Companion.minutes
import kotlin.time.Duration.Companion.nanoseconds
import kotlin.time.Duration.Companion.seconds
import kotlin.uuid.Uuid

@Immutable
@Inject
class PatternCollectionsSynchronizationPeriodUiEntryPoint(
    private val preferencesHolder: LoadedComposeLifePreferencesHolder,
    private val composeLifePreferences: ComposeLifePreferences,
) {
    @Suppress("ComposableNaming")
    @Composable
    operator fun invoke(
        modifier: Modifier = Modifier,
    ) = lambda(preferencesHolder, composeLifePreferences, modifier)

    companion object {
        private val lambda:
            @Composable context(LoadedComposeLifePreferencesHolder, ComposeLifePreferences) (
                modifier: Modifier,
            ) -> Unit =
            { modifier ->
                PatternCollectionsSynchronizationPeriodUi(modifier)
            }
    }
}

context(entryPoint: PatternCollectionsSynchronizationPeriodUiEntryPoint)
@Composable
fun PatternCollectionsSynchronizationPeriodUi(
    modifier: Modifier = Modifier,
) = entryPoint(modifier)

context(
    preferencesHolder: LoadedComposeLifePreferencesHolder,
composeLifePreferences: ComposeLifePreferences,
)
@Composable
private fun PatternCollectionsSynchronizationPeriodUi(
    modifier: Modifier = Modifier,
) {
    PatternCollectionsSynchronizationPeriodUi(
        patternCollectionsSynchronizationPeriodSessionValue =
        preferencesHolder.preferences.patternCollectionsSynchronizationPeriodSessionValue,
        setPatternCollectionsSynchronizationPeriodSessionValue =
        composeLifePreferences::setPatternCollectionsSynchronizationPeriod,
        modifier = modifier,
    )
}

@Composable
fun PatternCollectionsSynchronizationPeriodUi(
    patternCollectionsSynchronizationPeriodSessionValue: SessionValue<DateTimePeriod>,
    setPatternCollectionsSynchronizationPeriodSessionValue: suspend (
        expected: SessionValue<DateTimePeriod>?,
        newValue: SessionValue<DateTimePeriod>,
    ) -> Unit,
    modifier: Modifier = Modifier,
) {
    val resolver = parameterizedStringResolver()

    val patternCollectionsSynchronizationPeriodSessionValueHolder = rememberAsyncSessionValueHolder(
        upstreamSessionValue = patternCollectionsSynchronizationPeriodSessionValue,
        setUpstreamSessionValue = setPatternCollectionsSynchronizationPeriodSessionValue,
    )

    val localSessionId = patternCollectionsSynchronizationPeriodSessionValueHolder.info.localSessionId

    var synchronizationPeriodInMinutes by remember(localSessionId) {
        mutableStateOf(
            patternCollectionsSynchronizationPeriodSessionValueHolder.sessionValue.map { dateTimePeriod ->
                (dateTimePeriod.nanoseconds.nanoseconds +
                    dateTimePeriod.seconds.seconds +
                    dateTimePeriod.minutes.minutes +
                    dateTimePeriod.hours.hours +
                    dateTimePeriod.days.days +
                    ((dateTimePeriod.months / 12.0 + dateTimePeriod.years) * 365.2422).days).inWholeNanoseconds /
                    1.minutes.inWholeNanoseconds.toDouble()
            },
        )
    }

    EditableSlider(
        labelAndValueText = { parameterizedStringResource(
            Strings.PatternCollectionsSynchronizationPeriodLabelAndValue(it),
        ) },
        valueText = { resolver(Strings.PatternCollectionsSynchronizationPeriodValue(it)) },
        labelText = parameterizedStringResource(Strings.PatternCollectionsSynchronizationPeriod),
        textToValue = { it.toDoubleOrNull() },
        sessionValue = synchronizationPeriodInMinutes,
        onSessionValueChange = { _, newValue ->
            synchronizationPeriodInMinutes = newValue
            patternCollectionsSynchronizationPeriodSessionValueHolder.setValue(
                value = newValue.value.minutes.toDateTimePeriod(),
                valueId = newValue.valueId,
            )
        },
        modifier = modifier,
        valueRange = 15.0..7.days.inWholeMinutes.toDouble(),
        sliderBijection = PatternCollectionsSynchronizationPeriodBijection,
        suffix = { Text(parameterizedStringResource(Strings.PatternCollectionsSynchronizationPeriodSuffix)) },
        inputTransformation = InputTransformation.nonNegativeDouble(),
    )
}

private object PatternCollectionsSynchronizationPeriodBijection : SliderBijection<Double> {
    override fun valueToSlider(value: Double): Float = log2(value).toFloat()
    override fun sliderToValue(sliderValue: Float): Double = 2.0.pow(sliderValue.toDouble())
}
