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

package com.alexvanyo.composelife.ui.app.action

import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.setValue
import androidx.compose.ui.semantics.ProgressBarRangeInfo
import androidx.compose.ui.semantics.SemanticsActions
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.assert
import androidx.compose.ui.test.assertIsNotFocused
import androidx.compose.ui.test.assertTextContains
import androidx.compose.ui.test.hasImeAction
import androidx.compose.ui.test.hasProgressBarRangeInfo
import androidx.compose.ui.test.hasSetTextAction
import androidx.compose.ui.test.hasText
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.performImeAction
import androidx.compose.ui.test.performSemanticsAction
import androidx.compose.ui.test.performTextReplacement
import androidx.compose.ui.test.runComposeUiTest
import androidx.compose.ui.text.input.ImeAction
import com.alexvanyo.composelife.kmpandroidrunner.KmpAndroidJUnit4
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResolver
import com.alexvanyo.composelife.ui.app.resources.GenerationsPerStepLabel
import com.alexvanyo.composelife.ui.app.resources.GenerationsPerStepLabelAndValue
import com.alexvanyo.composelife.ui.app.resources.GenerationsPerStepValue
import com.alexvanyo.composelife.ui.app.resources.Strings
import com.alexvanyo.composelife.ui.app.resources.TargetStepsPerSecondLabel
import com.alexvanyo.composelife.ui.app.resources.TargetStepsPerSecondLabelAndValue
import com.alexvanyo.composelife.ui.app.resources.TargetStepsPerSecondValue
import org.junit.runner.RunWith
import kotlin.math.log2
import kotlin.test.Test

@OptIn(ExperimentalTestApi::class)
@RunWith(KmpAndroidJUnit4::class)
class InlineSpeedPaneTests {

    @Test
    fun target_steps_per_second_is_displayed_correctly() = runComposeUiTest {
        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            var targetStepsPerSecond by remember { mutableStateOf(60.0) }
            var generationsPerStep by remember { mutableStateOf(1) }

            InlineSpeedPane(
                targetStepsPerSecond = targetStepsPerSecond,
                setTargetStepsPerSecond = { targetStepsPerSecond = it },
                generationsPerStep = generationsPerStep,
                setGenerationsPerStep = { generationsPerStep = it },
            )
        }

        onNode(
            hasSetTextAction() and hasImeAction(ImeAction.Done) and
                hasText(resolver(Strings.TargetStepsPerSecondLabel)),
        )
            .assertTextContains(resolver(Strings.TargetStepsPerSecondValue(60.0)))
            .assertIsNotFocused()

        onNodeWithContentDescription(
            resolver(Strings.TargetStepsPerSecondLabelAndValue(60.0)),
        )
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = log2(60f), range = 0f..8f)))
    }

    @Test
    fun target_steps_per_second_updates_correctly_with_slider() = runComposeUiTest {
        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            var targetStepsPerSecond by remember { mutableStateOf(60.0) }
            var generationsPerStep by remember { mutableStateOf(1) }

            InlineSpeedPane(
                targetStepsPerSecond = targetStepsPerSecond,
                setTargetStepsPerSecond = { targetStepsPerSecond = it },
                generationsPerStep = generationsPerStep,
                setGenerationsPerStep = { generationsPerStep = it },
            )
        }

        onNodeWithContentDescription(
            resolver(Strings.TargetStepsPerSecondLabelAndValue(60.0)),
        )
            .performSemanticsAction(SemanticsActions.SetProgress) {
                it(8f)
            }

        onNode(
            hasSetTextAction() and hasImeAction(ImeAction.Done) and
                hasText(resolver(Strings.TargetStepsPerSecondLabel)),
        )
            .assertTextContains(resolver(Strings.TargetStepsPerSecondValue(256.0)))
            .assertIsNotFocused()

        onNodeWithContentDescription(
            resolver(Strings.TargetStepsPerSecondLabelAndValue(256.0)),
        )
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 8f, range = 0f..8f)))
    }

    @Test
    fun target_steps_per_second_updates_correctly_with_text() = runComposeUiTest {
        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            var targetStepsPerSecond by remember { mutableStateOf(60.0) }
            var generationsPerStep by remember { mutableStateOf(1) }

            InlineSpeedPane(
                targetStepsPerSecond = targetStepsPerSecond,
                setTargetStepsPerSecond = { targetStepsPerSecond = it },
                generationsPerStep = generationsPerStep,
                setGenerationsPerStep = { generationsPerStep = it },
            )
        }

        onNode(
            hasSetTextAction() and hasImeAction(ImeAction.Done) and
                hasText(resolver(Strings.TargetStepsPerSecondLabel)),
        )
            .performTextReplacement("256")
        onNode(
            hasSetTextAction() and hasImeAction(ImeAction.Done) and
                hasText(resolver(Strings.TargetStepsPerSecondLabel)),
        )
            .performImeAction()

        onNode(
            hasSetTextAction() and hasImeAction(ImeAction.Done) and
                hasText(resolver(Strings.TargetStepsPerSecondLabel)),
        )
            .assertTextContains(resolver(Strings.TargetStepsPerSecondValue(256.0)))
            .assertIsNotFocused()
        onNodeWithContentDescription(
            resolver(Strings.TargetStepsPerSecondLabelAndValue(256.0)),
        )
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 8f, range = 0f..8f)))
    }

    @Test
    fun generations_per_step_is_displayed_correctly() = runComposeUiTest {
        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            var targetStepsPerSecond by remember { mutableStateOf(60.0) }
            var generationsPerStep by remember { mutableStateOf(1) }

            InlineSpeedPane(
                targetStepsPerSecond = targetStepsPerSecond,
                setTargetStepsPerSecond = { targetStepsPerSecond = it },
                generationsPerStep = generationsPerStep,
                setGenerationsPerStep = { generationsPerStep = it },
            )
        }

        onNode(
            hasSetTextAction() and hasImeAction(ImeAction.Done) and
                hasText(resolver(Strings.GenerationsPerStepLabel)),
        )
            .assertTextContains(resolver(Strings.GenerationsPerStepValue(1)))
            .assertIsNotFocused()
        onNodeWithContentDescription(
            resolver(Strings.GenerationsPerStepLabelAndValue(1)),
        )
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 0f, range = 0f..8f, steps = 7)))
    }

    @Test
    fun generations_per_step_updates_correctly_with_slider() = runComposeUiTest {
        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            var targetStepsPerSecond by remember { mutableStateOf(60.0) }
            var generationsPerStep by remember { mutableStateOf(1) }

            InlineSpeedPane(
                targetStepsPerSecond = targetStepsPerSecond,
                setTargetStepsPerSecond = { targetStepsPerSecond = it },
                generationsPerStep = generationsPerStep,
                setGenerationsPerStep = { generationsPerStep = it },
            )
        }

        onNodeWithContentDescription(
            resolver(Strings.GenerationsPerStepLabelAndValue(1)),
        )
            .performSemanticsAction(SemanticsActions.SetProgress) {
                it(8f)
            }

        onNode(
            hasSetTextAction() and hasImeAction(ImeAction.Done) and
                hasText(resolver(Strings.GenerationsPerStepLabel)),
        )
            .assertTextContains(resolver(Strings.GenerationsPerStepValue(256)))
            .assertIsNotFocused()
        onNodeWithContentDescription(
            resolver(Strings.GenerationsPerStepLabelAndValue(256)),
        )
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 8f, range = 0f..8f, steps = 7)))
    }

    @Test
    fun generations_per_step_updates_correctly_with_text() = runComposeUiTest {
        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            var targetStepsPerSecond by remember { mutableStateOf(60.0) }
            var generationsPerStep by remember { mutableStateOf(1) }

            InlineSpeedPane(
                targetStepsPerSecond = targetStepsPerSecond,
                setTargetStepsPerSecond = { targetStepsPerSecond = it },
                generationsPerStep = generationsPerStep,
                setGenerationsPerStep = { generationsPerStep = it },
            )
        }

        onNode(
            hasSetTextAction() and hasImeAction(ImeAction.Done) and
                hasText(resolver(Strings.GenerationsPerStepLabel)),
        )
            .performTextReplacement("256")
        onNode(
            hasSetTextAction() and hasImeAction(ImeAction.Done) and
                hasText(resolver(Strings.GenerationsPerStepLabel)),
        )
            .performImeAction()

        onNode(
            hasSetTextAction() and hasImeAction(ImeAction.Done) and
                hasText(resolver(Strings.GenerationsPerStepLabel)),
        )
            .assertTextContains(resolver(Strings.GenerationsPerStepValue(256)))
            .assertIsNotFocused()
        onNodeWithContentDescription(
            resolver(Strings.GenerationsPerStepLabelAndValue(256)),
        )
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 8f, range = 0f..8f, steps = 7)))
    }
}
