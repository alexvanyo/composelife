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

package com.alexvanyo.composelife.ui.settings

import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.compose.ui.semantics.ProgressBarRangeInfo
import androidx.compose.ui.semantics.SemanticsActions
import androidx.compose.ui.semantics.SemanticsProperties
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.SemanticsMatcher
import androidx.compose.ui.test.assert
import androidx.compose.ui.test.assertIsNotFocused
import androidx.compose.ui.test.hasImeAction
import androidx.compose.ui.test.hasProgressBarRangeInfo
import androidx.compose.ui.test.hasSetTextAction
import androidx.compose.ui.test.hasText
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.onNodeWithText
import androidx.compose.ui.test.performSemanticsAction
import androidx.compose.ui.text.AnnotatedString
import androidx.compose.ui.text.input.ImeAction
import com.alexvanyo.composelife.kmpandroidrunner.BaseKmpTest
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResolver
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferences
import com.alexvanyo.composelife.preferences.TestComposeLifePreferences
import com.alexvanyo.composelife.sessionvalue.SessionValue
import com.alexvanyo.composelife.test.runComposeUiTest
import com.alexvanyo.composelife.ui.settings.resources.PatternCollectionsSynchronizationPeriod
import com.alexvanyo.composelife.ui.settings.resources.PatternCollectionsSynchronizationPeriodLabelAndValue
import com.alexvanyo.composelife.ui.settings.resources.PatternCollectionsSynchronizationPeriodSuffix
import com.alexvanyo.composelife.ui.settings.resources.Strings
import kotlinx.datetime.DateTimePeriod
import kotlin.math.log2
import kotlin.test.Test
import kotlin.test.assertTrue
import kotlin.time.Duration.Companion.days
import kotlin.uuid.Uuid

@OptIn(ExperimentalTestApi::class)
class PatternCollectionsSynchronizationPeriodUiTests : BaseKmpTest() {

    @Test
    fun pattern_collections_synchronization_period_is_displayed_correctly() {
        runComposeUiTest {
            lateinit var resolver: (ParameterizedString) -> String

            val sessionValue = SessionValue(
                sessionId = Uuid.random(),
                valueId = Uuid.random(),
                value = DateTimePeriod(hours = 24),
            )

            setContent {
                resolver = parameterizedStringResolver()
                PatternCollectionsSynchronizationPeriodUi(
                    patternCollectionsSynchronizationPeriodSessionValue = sessionValue,
                    setPatternCollectionsSynchronizationPeriodSessionValue = { _, _ -> },
                )
            }

            onNode(
                hasSetTextAction() and hasImeAction(ImeAction.Done) and
                    hasText(resolver(Strings.PatternCollectionsSynchronizationPeriod)),
            )
                .assert(SemanticsMatcher.expectValue(SemanticsProperties.EditableText, AnnotatedString("1440.0")))
                .assertIsNotFocused()

            onNodeWithText(resolver(Strings.PatternCollectionsSynchronizationPeriodSuffix))
                .assertExists()

            val expectedMin = log2(15.0).toFloat()
            val expectedMax = log2(7.days.inWholeMinutes.toDouble()).toFloat()
            val expectedCurrent = log2(1440.0).toFloat()

            onNodeWithContentDescription(
                resolver(Strings.PatternCollectionsSynchronizationPeriodLabelAndValue(1440.0)),
            )
                .assert(
                    hasProgressBarRangeInfo(
                        ProgressBarRangeInfo(
                            current = expectedCurrent,
                            range = expectedMin..expectedMax,
                        ),
                    ),
                )
        }
    }

    @Test
    fun pattern_collections_synchronization_period_slider_updates_state() {
        runComposeUiTest {
            lateinit var resolver: (ParameterizedString) -> String

            var sessionValue by mutableStateOf(
                SessionValue(
                    sessionId = Uuid.random(),
                    valueId = Uuid.random(),
                    value = DateTimePeriod(hours = 24),
                ),
            )

            setContent {
                resolver = parameterizedStringResolver()
                PatternCollectionsSynchronizationPeriodUi(
                    patternCollectionsSynchronizationPeriodSessionValue = sessionValue,
                    setPatternCollectionsSynchronizationPeriodSessionValue = { _, newValue ->
                        sessionValue = newValue
                    },
                )
            }

            val targetValue = 60.0
            val targetProgress = log2(targetValue).toFloat()

            val expectedMin = log2(15.0).toFloat()
            val expectedMax = log2(7.days.inWholeMinutes.toDouble()).toFloat()

            onNodeWithContentDescription(
                resolver(Strings.PatternCollectionsSynchronizationPeriodLabelAndValue(1440.0)),
            )
                .performSemanticsAction(SemanticsActions.SetProgress) {
                    assertTrue(it(targetProgress))
                }

            onNodeWithContentDescription(
                resolver(Strings.PatternCollectionsSynchronizationPeriodLabelAndValue(60.0)),
            )
                .assert(
                    hasProgressBarRangeInfo(
                        ProgressBarRangeInfo(
                            current = targetProgress,
                            range = expectedMin..expectedMax,
                        ),
                    ),
                )
        }
    }

    @Test
    fun pattern_collections_synchronization_period_with_context_is_displayed_correctly() {
        runComposeUiTest {
            lateinit var resolver: (ParameterizedString) -> String

            val composeLifePreferences = TestComposeLifePreferences(
                initialPreferences = LoadedComposeLifePreferences.Defaults.copy(
                    patternCollectionsSynchronizationPeriodSessionValue = SessionValue(
                        sessionId = Uuid.random(),
                        valueId = Uuid.random(),
                        value = DateTimePeriod(days = 1),
                    ),
                ),
            )

            setContent {
                resolver = parameterizedStringResolver()
                context(
                    PatternCollectionsSynchronizationPeriodUiCtx(
                        preferencesHolder = composeLifePreferences,
                        composeLifePreferences = composeLifePreferences,
                    ),
                ) {
                    PatternCollectionsSynchronizationPeriodUi()
                }
            }

            onNode(
                hasSetTextAction() and hasImeAction(ImeAction.Done) and
                    hasText(resolver(Strings.PatternCollectionsSynchronizationPeriod)),
            )
                .assert(SemanticsMatcher.expectValue(SemanticsProperties.EditableText, AnnotatedString("1440.0")))
                .assertIsNotFocused()
        }
    }

    @Test
    fun pattern_collections_synchronization_period_with_complex_period() {
        runComposeUiTest {
            lateinit var resolver: (ParameterizedString) -> String

            val sessionValue = SessionValue(
                sessionId = Uuid.random(),
                valueId = Uuid.random(),
                value = DateTimePeriod(
                    years = 1,
                    months = 6,
                    days = 2,
                    hours = 3,
                    minutes = 4,
                    seconds = 5,
                    nanoseconds = 6,
                ),
            )

            setContent {
                resolver = parameterizedStringResolver()
                PatternCollectionsSynchronizationPeriodUi(
                    patternCollectionsSynchronizationPeriodSessionValue = sessionValue,
                    setPatternCollectionsSynchronizationPeriodSessionValue = { _, _ -> },
                )
            }

            onNodeWithText(resolver(Strings.PatternCollectionsSynchronizationPeriodSuffix))
                .assertExists()
        }
    }
}
