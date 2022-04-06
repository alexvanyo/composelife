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

package com.alexvanyo.composelife.ui

import androidx.compose.foundation.layout.size
import androidx.compose.material3.windowsizeclass.ExperimentalMaterial3WindowSizeClassApi
import androidx.compose.material3.windowsizeclass.calculateWindowSizeClass
import androidx.compose.ui.Modifier
import androidx.compose.ui.test.hasAnyAncestor
import androidx.compose.ui.test.hasContentDescription
import androidx.compose.ui.test.hasTestTag
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.performClick
import androidx.compose.ui.unit.dp
import androidx.test.espresso.Espresso
import com.alexvanyo.composelife.algorithm.HashLifeAlgorithm
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.dispatchers.clock
import com.alexvanyo.composelife.model.rememberTemporalGameOfLifeState
import com.alexvanyo.composelife.model.rememberTemporalGameOfLifeStateMutator
import com.alexvanyo.composelife.test.BaseHiltTest
import com.alexvanyo.composelife.test.TestActivity
import dagger.hilt.android.testing.HiltAndroidTest
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.test.TestDispatcher
import org.junit.Test
import javax.inject.Inject

@OptIn(ExperimentalCoroutinesApi::class, ExperimentalMaterial3WindowSizeClassApi::class)
@HiltAndroidTest
class InteractiveCellUniverseInstrumentationTests : BaseHiltTest<TestActivity>(TestActivity::class.java) {

    @Inject
    lateinit var testDispatcher: TestDispatcher

    @Inject
    lateinit var dispatchers: ComposeLifeDispatchers

    @Test
    fun info_card_closes_upon_back_press() = runAppTest {
        val hashLifeAlgorithm = HashLifeAlgorithm(
            dispatchers = dispatchers,
        )

        composeTestRule.setContent {
            val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                isRunning = false,
                targetStepsPerSecond = 60.0,
            )

            rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = hashLifeAlgorithm,
                clock = testDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            InteractiveCellUniverse(
                temporalGameOfLifeState = temporalGameOfLifeState,
                windowSizeClass = calculateWindowSizeClass(activity = composeTestRule.activity),
                modifier = Modifier.size(480.dp),
            )
        }

        composeTestRule
            .onNode(
                hasAnyAncestor(hasTestTag("CellUniverseActionCard")) and
                    hasContentDescription(context.getString(R.string.expand)),
            )
            .performClick()

        composeTestRule.waitForIdle()

        Espresso.pressBack()

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.collapse))
            .assertDoesNotExist()
    }

    @Test
    fun action_card_closes_upon_back_press() = runAppTest {
        val hashLifeAlgorithm = HashLifeAlgorithm(
            dispatchers = dispatchers,
        )

        composeTestRule.setContent {
            val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                isRunning = false,
                targetStepsPerSecond = 60.0,
            )

            rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = hashLifeAlgorithm,
                clock = testDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            InteractiveCellUniverse(
                temporalGameOfLifeState = temporalGameOfLifeState,
                windowSizeClass = calculateWindowSizeClass(activity = composeTestRule.activity),
                modifier = Modifier.size(480.dp),
            )
        }

        composeTestRule
            .onNode(
                hasAnyAncestor(hasTestTag("CellUniverseActionCard")) and
                    hasContentDescription(context.getString(R.string.expand)),
            )
            .performClick()

        composeTestRule.waitForIdle()

        Espresso.pressBack()

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.collapse))
            .assertDoesNotExist()
    }
}
