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

package com.alexvanyo.composelife.ui.action

import android.content.Context
import androidx.activity.ComponentActivity
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.compose.ui.test.assertHasClickAction
import androidx.compose.ui.test.assertIsDisplayed
import androidx.compose.ui.test.assertIsOff
import androidx.compose.ui.test.assertIsOn
import androidx.compose.ui.test.junit4.createAndroidComposeRule
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.performClick
import androidx.test.ext.junit.runners.AndroidJUnit4
import com.alexvanyo.composelife.ui.R
import org.junit.Rule
import org.junit.Test
import org.junit.runner.RunWith
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

@RunWith(AndroidJUnit4::class)
class ActionControlRowTests {

    @get:Rule
    val composeTestRule = createAndroidComposeRule<ComponentActivity>()

    private val context: Context get() = composeTestRule.activity

    @Test
    fun false_values_are_displayed_correctly() {
        composeTestRule.setContent {
            ActionControlRow(
                isElevated = false,
                isRunning = false,
                setIsRunning = {},
                onStep = {},
                isExpanded = false,
                setIsExpanded = {},
                isViewportTracking = false,
                setIsViewportTracking = {},
            )
        }

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.play))
            .assertIsDisplayed()
            .assertHasClickAction()

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.step))
            .assertIsDisplayed()
            .assertHasClickAction()

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.expand))
            .assertIsDisplayed()
            .assertHasClickAction()

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.enable_autofit))
            .assertIsDisplayed()
            .assertIsOff()
            .assertHasClickAction()
    }

    @Test
    fun true_values_are_displayed_correctly() {
        composeTestRule.setContent {
            ActionControlRow(
                isElevated = false,
                isRunning = true,
                setIsRunning = {},
                onStep = {},
                isExpanded = true,
                setIsExpanded = {},
                isViewportTracking = true,
                setIsViewportTracking = {},
            )
        }

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.pause))
            .assertIsDisplayed()
            .assertHasClickAction()

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.step))
            .assertIsDisplayed()
            .assertHasClickAction()

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.collapse))
            .assertIsDisplayed()
            .assertHasClickAction()

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.disable_autofit))
            .assertIsDisplayed()
            .assertIsOn()
            .assertHasClickAction()
    }

    @Test
    fun on_step_updates_correctly() {
        var onStepCount = 0
        var isRunning by mutableStateOf(false)
        var isExpanded by mutableStateOf(false)
        var isViewportTracking by mutableStateOf(false)

        composeTestRule.setContent {
            ActionControlRow(
                isElevated = false,
                isRunning = isRunning,
                setIsRunning = { isRunning = it },
                onStep = { onStepCount++ },
                isExpanded = isExpanded,
                setIsExpanded = { isExpanded = it },
                isViewportTracking = isViewportTracking,
                setIsViewportTracking = { isViewportTracking = it },
            )
        }

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.step))
            .performClick()

        assertEquals(1, onStepCount)
    }

    @Test
    fun play_updates_correctly() {
        var isRunning by mutableStateOf(false)
        var isExpanded by mutableStateOf(false)
        var isViewportTracking by mutableStateOf(false)

        composeTestRule.setContent {
            ActionControlRow(
                isElevated = false,
                isRunning = isRunning,
                setIsRunning = { isRunning = it },
                onStep = {},
                isExpanded = isExpanded,
                setIsExpanded = { isExpanded = it },
                isViewportTracking = isViewportTracking,
                setIsViewportTracking = { isViewportTracking = it },
            )
        }

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.play))
            .performClick()

        assertTrue(isRunning)
    }

    @Test
    fun pause_updates_correctly() {
        var isRunning by mutableStateOf(true)
        var isExpanded by mutableStateOf(false)
        var isViewportTracking by mutableStateOf(false)

        composeTestRule.setContent {
            ActionControlRow(
                isElevated = false,
                isRunning = isRunning,
                setIsRunning = { isRunning = it },
                onStep = {},
                isExpanded = isExpanded,
                setIsExpanded = { isExpanded = it },
                isViewportTracking = isViewportTracking,
                setIsViewportTracking = { isViewportTracking = it },
            )
        }

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.pause))
            .performClick()

        assertFalse(isRunning)
    }

    @Test
    fun expand_updates_correctly() {
        var isRunning by mutableStateOf(false)
        var isExpanded by mutableStateOf(false)
        var isViewportTracking by mutableStateOf(false)

        composeTestRule.setContent {
            ActionControlRow(
                isElevated = false,
                isRunning = isRunning,
                setIsRunning = { isRunning = it },
                onStep = {},
                isExpanded = isExpanded,
                setIsExpanded = { isExpanded = it },
                isViewportTracking = isViewportTracking,
                setIsViewportTracking = { isViewportTracking = it },
            )
        }

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.expand))
            .performClick()

        assertTrue(isExpanded)
    }

    @Test
    fun collapse_updates_correctly() {
        var isRunning by mutableStateOf(false)
        var isExpanded by mutableStateOf(true)
        var isViewportTracking by mutableStateOf(false)

        composeTestRule.setContent {
            ActionControlRow(
                isElevated = false,
                isRunning = isRunning,
                setIsRunning = { isRunning = it },
                onStep = {},
                isExpanded = isExpanded,
                setIsExpanded = { isExpanded = it },
                isViewportTracking = isViewportTracking,
                setIsViewportTracking = { isViewportTracking = it },
            )
        }

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.collapse))
            .performClick()

        assertFalse(isExpanded)
    }

    @Test
    fun enable_autofit_correctly() {
        var isRunning by mutableStateOf(false)
        var isExpanded by mutableStateOf(false)
        var isViewportTracking by mutableStateOf(false)

        composeTestRule.setContent {
            ActionControlRow(
                isElevated = false,
                isRunning = isRunning,
                setIsRunning = { isRunning = it },
                onStep = {},
                isExpanded = isExpanded,
                setIsExpanded = { isExpanded = it },
                isViewportTracking = isViewportTracking,
                setIsViewportTracking = { isViewportTracking = it },
            )
        }

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.enable_autofit))
            .performClick()

        assertTrue(isViewportTracking)
    }

    @Test
    fun disable_autofit_updates_correctly() {
        var isRunning by mutableStateOf(false)
        var isExpanded by mutableStateOf(false)
        var isViewportTracking by mutableStateOf(true)

        composeTestRule.setContent {
            ActionControlRow(
                isElevated = false,
                isRunning = isRunning,
                setIsRunning = { isRunning = it },
                onStep = {},
                isExpanded = isExpanded,
                setIsExpanded = { isExpanded = it },
                isViewportTracking = isViewportTracking,
                setIsViewportTracking = { isViewportTracking = it },
            )
        }

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.disable_autofit))
            .performClick()

        assertFalse(isViewportTracking)
    }
}
