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

package com.alexvanyo.composelife.ui.app.action.settings

import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.assertHasClickAction
import androidx.compose.ui.test.assertIsOff
import androidx.compose.ui.test.assertIsOn
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.performClick
import androidx.compose.ui.test.runComposeUiTest
import com.alexvanyo.composelife.kmpandroidrunner.KmpAndroidJUnit4
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResolver
import com.alexvanyo.composelife.ui.app.resources.ClipboardWatchingOnboardingCompleted
import com.alexvanyo.composelife.ui.app.resources.Strings
import org.junit.runner.RunWith
import kotlin.test.Test
import kotlin.test.assertFalse
import kotlin.test.assertTrue

@OptIn(ExperimentalTestApi::class)
@RunWith(KmpAndroidJUnit4::class)
class ClipboardWatchingOnboardingCompletedUiTests {

    @Test
    fun not_completed_is_displayed_correctly() = runComposeUiTest {
        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            ClipboardWatchingOnboardingCompletedUi(
                completedClipboardWatchingOnboarding = false,
                setCompletedClipboardWatchingOnboarding = {},
            )
        }

        onNodeWithContentDescription(resolver(Strings.ClipboardWatchingOnboardingCompleted))
            .assertExists()
            .assertIsOff()
            .assertHasClickAction()
    }

    @Test
    fun not_completed_will_update_correctly() = runComposeUiTest {
        var completedClipboardWatchingOnboarding by mutableStateOf(false)

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            ClipboardWatchingOnboardingCompletedUi(
                completedClipboardWatchingOnboarding = completedClipboardWatchingOnboarding,
                setCompletedClipboardWatchingOnboarding = {
                    completedClipboardWatchingOnboarding = it
                },
            )
        }

        onNodeWithContentDescription(resolver(Strings.ClipboardWatchingOnboardingCompleted))
            .performClick()

        assertTrue(completedClipboardWatchingOnboarding)
    }

    @Test
    fun completed_is_displayed_correctly() = runComposeUiTest {
        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            ClipboardWatchingOnboardingCompletedUi(
                completedClipboardWatchingOnboarding = true,
                setCompletedClipboardWatchingOnboarding = {},
            )
        }

        onNodeWithContentDescription(resolver(Strings.ClipboardWatchingOnboardingCompleted))
            .assertExists()
            .assertIsOn()
            .assertHasClickAction()
    }

    @Test
    fun completed_will_update_correctly() = runComposeUiTest {
        var completedClipboardWatchingOnboarding by mutableStateOf(true)

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            ClipboardWatchingOnboardingCompletedUi(
                completedClipboardWatchingOnboarding = completedClipboardWatchingOnboarding,
                setCompletedClipboardWatchingOnboarding = {
                    completedClipboardWatchingOnboarding = it
                },
            )
        }

        onNodeWithContentDescription(resolver(Strings.ClipboardWatchingOnboardingCompleted))
            .performClick()

        assertFalse(completedClipboardWatchingOnboarding)
    }
}
