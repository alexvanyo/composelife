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

import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.ui.Modifier
import androidx.compose.ui.semantics.SemanticsActions
import androidx.compose.ui.test.SemanticsMatcher
import androidx.compose.ui.test.assertIsOn
import androidx.compose.ui.test.click
import androidx.compose.ui.test.filterToOne
import androidx.compose.ui.test.hasContentDescription
import androidx.compose.ui.test.onChildren
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.onNodeWithTag
import androidx.compose.ui.test.onNodeWithText
import androidx.compose.ui.test.performClick
import androidx.compose.ui.test.performSemanticsAction
import androidx.compose.ui.test.performTouchInput
import androidx.compose.ui.unit.IntOffset
import com.alexvanyo.composelife.algorithm.HashLifeAlgorithm
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.dispatchers.clock
import com.alexvanyo.composelife.model.rememberTemporalGameOfLifeState
import com.alexvanyo.composelife.model.rememberTemporalGameOfLifeStateMutator
import com.alexvanyo.composelife.patterns.SixLongLinePattern
import com.alexvanyo.composelife.test.BaseHiltTest
import com.alexvanyo.composelife.test.TestActivity
import dagger.hilt.android.testing.HiltAndroidTest
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.test.TestDispatcher
import org.junit.Test
import javax.inject.Inject

@OptIn(ExperimentalCoroutinesApi::class)
@HiltAndroidTest
class InteractiveCellUniverseTests : BaseHiltTest<TestActivity>(TestActivity::class.java) {

    @Inject
    lateinit var testDispatcher: TestDispatcher

    @Inject
    lateinit var dispatchers: ComposeLifeDispatchers

    @Test
    fun six_long_line_evolves_correctly() = runAppTest {
        val hashLifeAlgorithm = HashLifeAlgorithm(
            dispatchers = dispatchers
        )

        composeTestRule.setContent {
            val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                targetStepsPerSecond = 60.0
            )

            rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = hashLifeAlgorithm,
                clock = testDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            InteractiveCellUniverse(
                temporalGameOfLifeState = temporalGameOfLifeState,
                modifier = Modifier.fillMaxSize(),
                preferences = preferences,
            )
        }

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.pause))
            .performClick()

        SixLongLinePattern.seedCellState.offsetBy(IntOffset(-4, -3)).aliveCells.forEach { cell ->
            composeTestRule
                .onNodeWithContentDescription(
                    context.getString(R.string.cell_content_description, cell.x, cell.y)
                )
                .performTouchInput { click(topLeft) }
        }

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.play))
            .performClick()

        SixLongLinePattern.cellStates.forEach { expectedCellState ->
            testDispatcher.scheduler.advanceTimeBy(16)
            testDispatcher.scheduler.runCurrent()
            composeTestRule.waitForIdle()

            expectedCellState.offsetBy(IntOffset(-4, -3)).aliveCells.forEach { cell ->
                composeTestRule
                    .onNodeWithContentDescription(
                        context.getString(R.string.cell_content_description, cell.x, cell.y)
                    )
                    .assertIsOn()
            }
        }
    }

    @Test
    fun six_long_line_evolves_correctly_after_slowing_down() = runAppTest {
        val hashLifeAlgorithm = HashLifeAlgorithm(
            dispatchers = dispatchers
        )

        composeTestRule.setContent {
            val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                targetStepsPerSecond = 60.0
            )

            rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = hashLifeAlgorithm,
                clock = testDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            InteractiveCellUniverse(
                temporalGameOfLifeState = temporalGameOfLifeState,
                modifier = Modifier.fillMaxSize(),
                preferences = preferences,
            )
        }

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.pause))
            .performClick()

        SixLongLinePattern.seedCellState.offsetBy(IntOffset(-4, -3)).aliveCells.forEach { cell ->
            composeTestRule
                .onNodeWithContentDescription(
                    context.getString(R.string.cell_content_description, cell.x, cell.y)
                )
                .performTouchInput { click(topLeft) }
        }

        composeTestRule
            .onNodeWithTag("CellUniverseActionCard")
            .onChildren()
            .filterToOne(hasContentDescription(context.getString(R.string.expand)))
            .performClick()

        composeTestRule
            .onNodeWithText(context.getString(R.string.target_steps_per_second, 60.0))
            .onChildren()
            .filterToOne(SemanticsMatcher.keyIsDefined(SemanticsActions.SetProgress))
            .performSemanticsAction(SemanticsActions.SetProgress) { it(0f) }

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.play))
            .performClick()

        SixLongLinePattern.cellStates.forEach { expectedCellState ->
            testDispatcher.scheduler.advanceTimeBy(1000)
            testDispatcher.scheduler.runCurrent()
            composeTestRule.waitForIdle()

            expectedCellState.offsetBy(IntOffset(-4, -3)).aliveCells.forEach { cell ->
                composeTestRule
                    .onNodeWithContentDescription(
                        context.getString(R.string.cell_content_description, cell.x, cell.y)
                    )
                    .assertIsOn()
            }
        }
    }

    @Test
    fun six_long_line_evolves_correctly_with_step() = runAppTest {
        val hashLifeAlgorithm = HashLifeAlgorithm(
            dispatchers = dispatchers
        )

        composeTestRule.setContent {
            val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                targetStepsPerSecond = 0.001
            )

            rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = hashLifeAlgorithm,
                clock = testDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            InteractiveCellUniverse(
                temporalGameOfLifeState = temporalGameOfLifeState,
                modifier = Modifier.fillMaxSize(),
                preferences = preferences,
            )
        }

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.pause))
            .performClick()

        SixLongLinePattern.seedCellState.offsetBy(IntOffset(-4, -3)).aliveCells.forEach { cell ->
            composeTestRule
                .onNodeWithContentDescription(
                    context.getString(R.string.cell_content_description, cell.x, cell.y)
                )
                .performTouchInput { click(topLeft) }
        }

        SixLongLinePattern.cellStates.forEach { expectedCellState ->
            composeTestRule
                .onNodeWithContentDescription(context.getString(R.string.step))
                .performClick()

            testDispatcher.scheduler.runCurrent()
            composeTestRule.waitForIdle()

            expectedCellState.offsetBy(IntOffset(-4, -3)).aliveCells.forEach { cell ->
                composeTestRule
                    .onNodeWithContentDescription(
                        context.getString(R.string.cell_content_description, cell.x, cell.y)
                    )
                    .assertIsOn()
            }
        }
    }

    @Test
    fun six_long_line_evolves_correctly_with_double_step() = runAppTest {
        val hashLifeAlgorithm = HashLifeAlgorithm(
            dispatchers = dispatchers
        )

        composeTestRule.setContent {
            val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                targetStepsPerSecond = 0.001
            )

            rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = hashLifeAlgorithm,
                clock = testDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            InteractiveCellUniverse(
                temporalGameOfLifeState = temporalGameOfLifeState,
                modifier = Modifier.fillMaxSize(),
                preferences = preferences,
            )
        }

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.pause))
            .performClick()

        SixLongLinePattern.seedCellState.offsetBy(IntOffset(-4, -3)).aliveCells.forEach { cell ->
            composeTestRule
                .onNodeWithContentDescription(
                    context.getString(R.string.cell_content_description, cell.x, cell.y)
                )
                .performTouchInput { click(topLeft) }
        }

        composeTestRule
            .onNodeWithTag("CellUniverseActionCard")
            .onChildren()
            .filterToOne(hasContentDescription(context.getString(R.string.expand)))
            .performClick()

        composeTestRule
            .onNodeWithText(context.getString(R.string.generations_per_step, 1))
            .onChildren()
            .filterToOne(SemanticsMatcher.keyIsDefined(SemanticsActions.SetProgress))
            .performSemanticsAction(SemanticsActions.SetProgress) { it(1f) }

        SixLongLinePattern.cellStates.filterIndexed { index, _ -> index.rem(2) == 1 }.forEach { expectedCellState ->
            composeTestRule
                .onNodeWithContentDescription(context.getString(R.string.step))
                .performClick()

            testDispatcher.scheduler.runCurrent()
            composeTestRule.waitForIdle()

            expectedCellState.offsetBy(IntOffset(-4, -3)).aliveCells.forEach { cell ->
                composeTestRule
                    .onNodeWithContentDescription(
                        context.getString(R.string.cell_content_description, cell.x, cell.y)
                    )
                    .assertIsOn()
            }
        }
    }
}
