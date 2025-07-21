/*
 * Copyright 2024 The Android Open Source Project
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

package com.alexvanyo.composelife.ui.mobile.component

import androidx.compose.foundation.layout.Column
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.compose.ui.semantics.ProgressBarRangeInfo
import androidx.compose.ui.semantics.SemanticsActions
import androidx.compose.ui.semantics.SemanticsProperties
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.SemanticsMatcher
import androidx.compose.ui.test.assert
import androidx.compose.ui.test.assertIsFocused
import androidx.compose.ui.test.assertIsNotFocused
import androidx.compose.ui.test.hasImeAction
import androidx.compose.ui.test.hasProgressBarRangeInfo
import androidx.compose.ui.test.hasSetTextAction
import androidx.compose.ui.test.hasText
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.performImeAction
import androidx.compose.ui.test.performSemanticsAction
import androidx.compose.ui.test.performTextClearance
import androidx.compose.ui.test.performTextReplacement
import androidx.compose.ui.test.runComposeUiTest
import androidx.compose.ui.text.AnnotatedString
import androidx.compose.ui.text.input.ImeAction
import com.alexvanyo.composelife.kmpandroidrunner.KmpAndroidJUnit4
import com.alexvanyo.composelife.sessionvalue.SessionValue
import org.junit.runner.RunWith
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.uuid.Uuid

@OptIn(ExperimentalTestApi::class)
@RunWith(KmpAndroidJUnit4::class)
class EditableSliderTests {

    @Test
    fun is_displayed_correctly() = runComposeUiTest {
        var sessionValue by mutableStateOf(SessionValue(Uuid.random(), Uuid.random(), 0f))

        setContent {
            EditableSlider(
                labelAndValueText = { "float: $it" },
                valueText = { it.toString() },
                labelText = "float",
                textToValue = String::toFloatOrNull,
                sessionValue = sessionValue,
                onSessionValueChange = { _, newValue ->
                    sessionValue = newValue
                },
                valueRange = 0f..1f,
                sliderBijection = Float.IdentitySliderBijection,
            )
        }

        onNode(hasSetTextAction() and hasImeAction(ImeAction.Done) and hasText("float"))
            .assert(SemanticsMatcher.expectValue(SemanticsProperties.EditableText, AnnotatedString("0.0")))
            .assertIsNotFocused()
        onNodeWithContentDescription("float: 0.0")
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 0.0f, range = 0f..1f)))
    }

    @Test
    fun is_updated_correctly_with_slider() = runComposeUiTest {
        var sessionValue by mutableStateOf(SessionValue(Uuid.random(), Uuid.random(), 0f))

        setContent {
            EditableSlider(
                labelAndValueText = { "float: $it" },
                valueText = { it.toString() },
                labelText = "float",
                textToValue = String::toFloatOrNull,
                sessionValue = sessionValue,
                onSessionValueChange = { _, newValue ->
                    sessionValue = newValue
                },
                valueRange = 0f..1f,
                sliderBijection = Float.IdentitySliderBijection,
            )
        }

        onNodeWithContentDescription("float: 0.0")
            .performSemanticsAction(SemanticsActions.SetProgress) {
                it(0.5f)
            }

        onNode(hasSetTextAction() and hasImeAction(ImeAction.Done) and hasText("float"))
            .assert(SemanticsMatcher.expectValue(SemanticsProperties.EditableText, AnnotatedString("0.5")))
            .assertIsNotFocused()
        onNodeWithContentDescription("float: 0.5")
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 0.5f, range = 0f..1f)))

        assertEquals(0.5f, sessionValue.value)
    }

    @Test
    fun is_updated_correctly_with_text() = runComposeUiTest {
        var sessionValue by mutableStateOf(SessionValue(Uuid.random(), Uuid.random(), 0f))

        setContent {
            EditableSlider(
                labelAndValueText = { "float: $it" },
                valueText = { it.toString() },
                labelText = "float",
                textToValue = String::toFloatOrNull,
                sessionValue = sessionValue,
                onSessionValueChange = { _, newValue ->
                    sessionValue = newValue
                },
                valueRange = 0f..1f,
                sliderBijection = Float.IdentitySliderBijection,
            )
        }

        onNode(hasSetTextAction() and hasImeAction(ImeAction.Done) and hasText("float"))
            .performTextReplacement("0.5")

        onNode(hasSetTextAction() and hasImeAction(ImeAction.Done) and hasText("float"))
            .assert(SemanticsMatcher.expectValue(SemanticsProperties.EditableText, AnnotatedString("0.5")))
            .assertIsFocused()
        onNodeWithContentDescription("float: 0.5")
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 0.5f, range = 0f..1f)))
        assertEquals(0.5f, sessionValue.value)

        onNode(hasSetTextAction() and hasImeAction(ImeAction.Done) and hasText("float"))
            .performImeAction()

        onNode(hasSetTextAction() and hasImeAction(ImeAction.Done) and hasText("float"))
            .assert(SemanticsMatcher.expectValue(SemanticsProperties.EditableText, AnnotatedString("0.5")))
            .assertIsNotFocused()
        onNodeWithContentDescription("float: 0.5")
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 0.5f, range = 0f..1f)))
        assertEquals(0.5f, sessionValue.value)
    }

    @Test
    fun is_updated_correctly_with_text_clearing() = runComposeUiTest {
        var sessionValue by mutableStateOf(SessionValue(Uuid.random(), Uuid.random(), 0.5f))

        setContent {
            EditableSlider(
                labelAndValueText = { "float: $it" },
                valueText = { it.toString() },
                labelText = "float",
                textToValue = String::toFloatOrNull,
                sessionValue = sessionValue,
                onSessionValueChange = { _, newValue ->
                    sessionValue = newValue
                },
                valueRange = 0f..1f,
                sliderBijection = Float.IdentitySliderBijection,
            )
        }

        onNode(hasSetTextAction() and hasImeAction(ImeAction.Done) and hasText("float"))
            .performTextClearance()

        onNode(hasSetTextAction() and hasImeAction(ImeAction.Done) and hasText("float"))
            .assert(SemanticsMatcher.expectValue(SemanticsProperties.EditableText, AnnotatedString("")))
            .assertIsFocused()
        onNodeWithContentDescription("float: 0.5")
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 0.5f, range = 0f..1f)))
        assertEquals(0.5f, sessionValue.value)

        onNode(hasSetTextAction() and hasImeAction(ImeAction.Done) and hasText("float"))
            .performImeAction()

        onNode(hasSetTextAction() and hasImeAction(ImeAction.Done) and hasText("float"))
            .assert(SemanticsMatcher.expectValue(SemanticsProperties.EditableText, AnnotatedString("0.5")))
            .assertIsNotFocused()
        onNodeWithContentDescription("float: 0.5")
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 0.5f, range = 0f..1f)))
        assertEquals(0.5f, sessionValue.value)
    }

    @Test
    fun is_updated_correctly_with_text_out_of_range() = runComposeUiTest {
        var sessionValue by mutableStateOf(SessionValue(Uuid.random(), Uuid.random(), 0.5f))

        setContent {
            EditableSlider(
                labelAndValueText = { "float: $it" },
                valueText = { it.toString() },
                labelText = "float",
                textToValue = String::toFloatOrNull,
                sessionValue = sessionValue,
                onSessionValueChange = { _, newValue ->
                    sessionValue = newValue
                },
                valueRange = 0f..1f,
                sliderBijection = Float.IdentitySliderBijection,
            )
        }

        onNode(hasSetTextAction() and hasImeAction(ImeAction.Done) and hasText("float"))
            .performTextReplacement("2.5")

        onNode(hasSetTextAction() and hasImeAction(ImeAction.Done) and hasText("float"))
            .assert(SemanticsMatcher.expectValue(SemanticsProperties.EditableText, AnnotatedString("2.5")))
            .assertIsFocused()
        onNodeWithContentDescription("float: 1.0")
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 1f, range = 0f..1f)))
        assertEquals(1f, sessionValue.value)

        onNode(hasSetTextAction() and hasImeAction(ImeAction.Done) and hasText("float"))
            .performImeAction()

        onNode(hasSetTextAction() and hasImeAction(ImeAction.Done) and hasText("float"))
            .assert(SemanticsMatcher.expectValue(SemanticsProperties.EditableText, AnnotatedString("1.0")))
            .assertIsNotFocused()
        onNodeWithContentDescription("float: 1.0")
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 1f, range = 0f..1f)))
        assertEquals(1f, sessionValue.value)
    }

    @Suppress("LongMethod")
    @Test
    fun multiple_concurrent_editable_sliders_are_updated_correctly_with_slider() = runComposeUiTest {
        var sessionValue by mutableStateOf(SessionValue(Uuid.random(), Uuid.random(), 0f))

        setContent {
            Column {
                EditableSlider(
                    labelAndValueText = { "float 1: $it" },
                    valueText = { it.toString() },
                    labelText = "float 1",
                    textToValue = String::toFloatOrNull,
                    sessionValue = sessionValue,
                    onSessionValueChange = { _, newValue ->
                        sessionValue = newValue
                    },
                    valueRange = 0f..1f,
                    sliderBijection = Float.IdentitySliderBijection,
                )
                EditableSlider(
                    labelAndValueText = { "float 2: $it" },
                    valueText = { it.toString() },
                    labelText = "float 2",
                    textToValue = String::toFloatOrNull,
                    sessionValue = sessionValue,
                    onSessionValueChange = { _, newValue ->
                        sessionValue = newValue
                    },
                    valueRange = 0f..1f,
                    sliderBijection = Float.IdentitySliderBijection,
                )
            }
        }

        onNodeWithContentDescription("float 1: 0.0")
            .performSemanticsAction(SemanticsActions.SetProgress) {
                it(0.5f)
            }

        onNode(hasSetTextAction() and hasImeAction(ImeAction.Done) and hasText("float 1"))
            .assert(SemanticsMatcher.expectValue(SemanticsProperties.EditableText, AnnotatedString("0.5")))
            .assertIsNotFocused()
        onNodeWithContentDescription("float 1: 0.5")
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 0.5f, range = 0f..1f)))

        onNode(hasSetTextAction() and hasImeAction(ImeAction.Done) and hasText("float 2"))
            .assert(SemanticsMatcher.expectValue(SemanticsProperties.EditableText, AnnotatedString("0.5")))
            .assertIsNotFocused()
        onNodeWithContentDescription("float 2: 0.5")
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 0.5f, range = 0f..1f)))

        assertEquals(0.5f, sessionValue.value)

        onNodeWithContentDescription("float 2: 0.5")
            .performSemanticsAction(SemanticsActions.SetProgress) {
                it(0.25f)
            }

        onNode(hasSetTextAction() and hasImeAction(ImeAction.Done) and hasText("float 1"))
            .assert(SemanticsMatcher.expectValue(SemanticsProperties.EditableText, AnnotatedString("0.25")))
            .assertIsNotFocused()
        onNodeWithContentDescription("float 1: 0.25")
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 0.25f, range = 0f..1f)))

        onNode(hasSetTextAction() and hasImeAction(ImeAction.Done) and hasText("float 2"))
            .assert(SemanticsMatcher.expectValue(SemanticsProperties.EditableText, AnnotatedString("0.25")))
            .assertIsNotFocused()
        onNodeWithContentDescription("float 2: 0.25")
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 0.25f, range = 0f..1f)))

        assertEquals(0.25f, sessionValue.value)
    }

    @Suppress("LongMethod")
    @Test
    fun multiple_concurrent_editable_sliders_are_updated_correctly_with_text() = runComposeUiTest {
        var sessionValue by mutableStateOf(SessionValue(Uuid.random(), Uuid.random(), 0f))

        setContent {
            Column {
                EditableSlider(
                    labelAndValueText = { "float 1: $it" },
                    valueText = { it.toString() },
                    labelText = "float 1",
                    textToValue = String::toFloatOrNull,
                    sessionValue = sessionValue,
                    onSessionValueChange = { _, newValue ->
                        sessionValue = newValue
                    },
                    valueRange = 0f..1f,
                    sliderBijection = Float.IdentitySliderBijection,
                )
                EditableSlider(
                    labelAndValueText = { "float 2: $it" },
                    valueText = { it.toString() },
                    labelText = "float 2",
                    textToValue = String::toFloatOrNull,
                    sessionValue = sessionValue,
                    onSessionValueChange = { _, newValue ->
                        sessionValue = newValue
                    },
                    valueRange = 0f..1f,
                    sliderBijection = Float.IdentitySliderBijection,
                )
            }
        }

        onNode(hasSetTextAction() and hasImeAction(ImeAction.Done) and hasText("float 1"))
            .performTextReplacement("0.5")
        onNode(hasSetTextAction() and hasImeAction(ImeAction.Done) and hasText("float 1"))
            .performImeAction()

        onNode(hasSetTextAction() and hasImeAction(ImeAction.Done) and hasText("float 1"))
            .assert(SemanticsMatcher.expectValue(SemanticsProperties.EditableText, AnnotatedString("0.5")))
            .assertIsNotFocused()
        onNodeWithContentDescription("float 1: 0.5")
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 0.5f, range = 0f..1f)))

        onNode(hasSetTextAction() and hasImeAction(ImeAction.Done) and hasText("float 2"))
            .assert(SemanticsMatcher.expectValue(SemanticsProperties.EditableText, AnnotatedString("0.5")))
            .assertIsNotFocused()
        onNodeWithContentDescription("float 2: 0.5")
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 0.5f, range = 0f..1f)))

        assertEquals(0.5f, sessionValue.value)

        onNode(hasSetTextAction() and hasImeAction(ImeAction.Done) and hasText("float 2"))
            .performTextReplacement("0.25")
        onNode(hasSetTextAction() and hasImeAction(ImeAction.Done) and hasText("float 2"))
            .performImeAction()

        onNode(hasSetTextAction() and hasImeAction(ImeAction.Done) and hasText("float 1"))
            .assert(SemanticsMatcher.expectValue(SemanticsProperties.EditableText, AnnotatedString("0.25")))
            .assertIsNotFocused()
        onNodeWithContentDescription("float 1: 0.25")
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 0.25f, range = 0f..1f)))

        onNode(hasSetTextAction() and hasImeAction(ImeAction.Done) and hasText("float 2"))
            .assert(SemanticsMatcher.expectValue(SemanticsProperties.EditableText, AnnotatedString("0.25")))
            .assertIsNotFocused()
        onNodeWithContentDescription("float 2: 0.25")
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 0.25f, range = 0f..1f)))

        assertEquals(0.25f, sessionValue.value)
    }
}
