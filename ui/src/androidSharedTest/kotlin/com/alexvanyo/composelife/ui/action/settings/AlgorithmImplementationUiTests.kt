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

package com.alexvanyo.composelife.ui.action.settings

import android.content.Context
import androidx.activity.ComponentActivity
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.compose.ui.test.assertHasClickAction
import androidx.compose.ui.test.hasAnyAncestor
import androidx.compose.ui.test.hasText
import androidx.compose.ui.test.isPopup
import androidx.compose.ui.test.junit4.createAndroidComposeRule
import androidx.compose.ui.test.onNodeWithText
import androidx.compose.ui.test.performClick
import androidx.test.ext.junit.runners.AndroidJUnit4
import com.alexvanyo.composelife.preferences.AlgorithmType
import com.alexvanyo.composelife.ui.R
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.test.runTest
import leakcanary.SkipLeakDetection
import org.junit.Rule
import org.junit.Test
import org.junit.runner.RunWith
import kotlin.test.assertEquals

@OptIn(ExperimentalCoroutinesApi::class)
@RunWith(AndroidJUnit4::class)
class AlgorithmImplementationUiTests {

    @get:Rule
    val composeTestRule = createAndroidComposeRule<ComponentActivity>()

    private val context: Context get() = composeTestRule.activity

    @Test
    fun naive_is_displayed_correctly() = runTest {
        composeTestRule.setContent {
            AlgorithmImplementationUi(
                algorithmChoice = AlgorithmType.NaiveAlgorithm,
                setAlgorithmChoice = {},
            )
        }

        composeTestRule
            .onNodeWithText(context.getString(R.string.naive_algorithm))
            .assertExists()
            .assertHasClickAction()
    }

    @Test
    fun hashlife_is_displayed_correctly() = runTest {
        composeTestRule.setContent {
            AlgorithmImplementationUi(
                algorithmChoice = AlgorithmType.HashLifeAlgorithm,
                setAlgorithmChoice = {},
            )
        }

        composeTestRule
            .onNodeWithText(context.getString(R.string.hash_life_algorithm))
            .assertExists()
            .assertHasClickAction()
    }

    @SkipLeakDetection("https://issuetracker.google.com/issues/206177594", "Inner")
    @Test
    fun algorithm_implementation_popup_displays_options() = runTest {
        var algorithmChoice: AlgorithmType by mutableStateOf(AlgorithmType.NaiveAlgorithm)

        composeTestRule.setContent {
            AlgorithmImplementationUi(
                algorithmChoice = algorithmChoice,
                setAlgorithmChoice = { algorithmChoice = it },
            )
        }

        composeTestRule
            .onNodeWithText(context.getString(R.string.naive_algorithm))
            .performClick()

        composeTestRule
            .onNode(hasAnyAncestor(isPopup()) and hasText(context.getString(R.string.hash_life_algorithm)))
            .assertHasClickAction()
            .performClick()

        assertEquals(AlgorithmType.HashLifeAlgorithm, algorithmChoice)

        composeTestRule
            .onNode(isPopup())
            .assertDoesNotExist()

        composeTestRule
            .onNodeWithText(context.getString(R.string.hash_life_algorithm))
            .assertExists()
            .assertHasClickAction()
    }
}
