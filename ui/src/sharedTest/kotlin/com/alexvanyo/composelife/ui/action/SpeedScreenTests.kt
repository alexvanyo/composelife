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

import android.app.Application
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.setValue
import androidx.compose.ui.semantics.ProgressBarRangeInfo
import androidx.compose.ui.semantics.SemanticsActions
import androidx.compose.ui.test.assert
import androidx.compose.ui.test.hasProgressBarRangeInfo
import androidx.compose.ui.test.junit4.createComposeRule
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.performSemanticsAction
import androidx.test.core.app.ApplicationProvider
import androidx.test.ext.junit.runners.AndroidJUnit4
import com.alexvanyo.composelife.ui.R
import org.junit.Rule
import org.junit.Test
import org.junit.runner.RunWith
import kotlin.math.log2

@RunWith(AndroidJUnit4::class)
class SpeedScreenTests {

    @get:Rule
    val composeTestRule = createComposeRule()

    private val applicationContext = ApplicationProvider.getApplicationContext<Application>()

    @Test
    fun speed_screen_preview() {
        composeTestRule.setContent {
            SpeedScreenPreview()
        }
    }

    @Test
    fun target_steps_per_second_is_displayed_correctly() {
        composeTestRule.setContent {
            var targetStepsPerSecond by remember { mutableStateOf(60.0) }
            var generationsPerStep by remember { mutableStateOf(1) }

            SpeedScreen(
                targetStepsPerSecond = targetStepsPerSecond,
                setTargetStepsPerSecond = { targetStepsPerSecond = it },
                generationsPerStep = generationsPerStep,
                setGenerationsPerStep = { generationsPerStep = it },
            )
        }

        composeTestRule
            .onNodeWithContentDescription(
                applicationContext.getString(R.string.target_steps_per_second, 60.0),
            )
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = log2(60f), range = 0f..8f)))
    }

    @Test
    fun target_steps_per_second_updates_correctly() {
        composeTestRule.setContent {
            var targetStepsPerSecond by remember { mutableStateOf(60.0) }
            var generationsPerStep by remember { mutableStateOf(1) }

            SpeedScreen(
                targetStepsPerSecond = targetStepsPerSecond,
                setTargetStepsPerSecond = { targetStepsPerSecond = it },
                generationsPerStep = generationsPerStep,
                setGenerationsPerStep = { generationsPerStep = it },
            )
        }

        composeTestRule
            .onNodeWithContentDescription(
                applicationContext.getString(R.string.target_steps_per_second, 60.0),
            )
            .performSemanticsAction(SemanticsActions.SetProgress) {
                it(8f)
            }

        composeTestRule
            .onNodeWithContentDescription(
                applicationContext.getString(R.string.target_steps_per_second, 256.0),
            )
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 8f, range = 0f..8f)))
    }

    @Test
    fun generations_per_step_is_displayed_correctly() {
        composeTestRule.setContent {
            var targetStepsPerSecond by remember { mutableStateOf(60.0) }
            var generationsPerStep by remember { mutableStateOf(1) }

            SpeedScreen(
                targetStepsPerSecond = targetStepsPerSecond,
                setTargetStepsPerSecond = { targetStepsPerSecond = it },
                generationsPerStep = generationsPerStep,
                setGenerationsPerStep = { generationsPerStep = it },
            )
        }

        composeTestRule
            .onNodeWithContentDescription(
                applicationContext.getString(R.string.generations_per_step, 1),
            )
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 0f, range = 0f..8f, steps = 7)))
    }

    @Test
    fun generations_per_step_updates_correctly() {
        composeTestRule.setContent {
            var targetStepsPerSecond by remember { mutableStateOf(60.0) }
            var generationsPerStep by remember { mutableStateOf(1) }

            SpeedScreen(
                targetStepsPerSecond = targetStepsPerSecond,
                setTargetStepsPerSecond = { targetStepsPerSecond = it },
                generationsPerStep = generationsPerStep,
                setGenerationsPerStep = { generationsPerStep = it },
            )
        }

        composeTestRule
            .onNodeWithContentDescription(
                applicationContext.getString(R.string.generations_per_step, 1),
            )
            .performSemanticsAction(SemanticsActions.SetProgress) {
                it(8f)
            }

        composeTestRule
            .onNodeWithContentDescription(
                applicationContext.getString(R.string.generations_per_step, 256),
            )
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo(current = 8f, range = 0f..8f, steps = 7)))
    }
}
