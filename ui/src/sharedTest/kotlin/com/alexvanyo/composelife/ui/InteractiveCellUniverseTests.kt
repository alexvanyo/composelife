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
import androidx.compose.foundation.layout.size
import androidx.compose.material3.windowsizeclass.ExperimentalMaterial3WindowSizeClassApi
import androidx.compose.material3.windowsizeclass.calculateWindowSizeClass
import androidx.compose.ui.Modifier
import androidx.compose.ui.semantics.SemanticsActions
import androidx.compose.ui.semantics.SemanticsActions.ScrollToIndex
import androidx.compose.ui.test.assertIsOn
import androidx.compose.ui.test.click
import androidx.compose.ui.test.hasAnyAncestor
import androidx.compose.ui.test.hasContentDescription
import androidx.compose.ui.test.hasTestTag
import androidx.compose.ui.test.onAllNodesWithContentDescription
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.onNodeWithTag
import androidx.compose.ui.test.performClick
import androidx.compose.ui.test.performSemanticsAction
import androidx.compose.ui.test.performTouchInput
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.dp
import androidx.test.espresso.Espresso
import com.alexvanyo.composelife.algorithm.GameOfLifeAlgorithm
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.dispatchers.clock
import com.alexvanyo.composelife.model.rememberTemporalGameOfLifeState
import com.alexvanyo.composelife.model.rememberTemporalGameOfLifeStateMutator
import com.alexvanyo.composelife.patterns.SixLongLinePattern
import com.alexvanyo.composelife.test.BaseHiltTest
import com.alexvanyo.composelife.test.TestActivity
import com.alexvanyo.composelife.ui.entrypoints.WithDependencies
import com.alexvanyo.composelife.util.toRingIndex
import dagger.hilt.android.testing.HiltAndroidTest
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.test.TestDispatcher
import leakcanary.SkipLeakDetection
import org.junit.Test
import javax.inject.Inject

@OptIn(ExperimentalCoroutinesApi::class, ExperimentalMaterial3WindowSizeClassApi::class)
@HiltAndroidTest
class InteractiveCellUniverseTests : BaseHiltTest<TestActivity>(TestActivity::class.java) {

    @Inject
    lateinit var testDispatcher: TestDispatcher

    @Inject
    lateinit var gameOfLifeAlgorithm: GameOfLifeAlgorithm

    @Inject
    lateinit var dispatchers: ComposeLifeDispatchers

    @SkipLeakDetection("appliedChanges", "Outer")
    @Test
    fun info_card_closes_upon_back_press() = runAppTest {
        composeTestRule.setContent {
            val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                isRunning = false,
                targetStepsPerSecond = 60.0,
            )

            rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = gameOfLifeAlgorithm,
                clock = testDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            WithDependencies(
                dispatchers = dispatchers,
                gameOfLifeAlgorithm = gameOfLifeAlgorithm,
                composeLifePreferences = preferences,
            ) {
                InteractiveCellUniverse(
                    temporalGameOfLifeState = temporalGameOfLifeState,
                    windowSizeClass = calculateWindowSizeClass(activity = composeTestRule.activity),
                    modifier = Modifier.size(480.dp),
                )
            }
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

    @SkipLeakDetection("appliedChanges", "Outer")
    @Test
    fun action_card_closes_upon_back_press() = runAppTest {
        composeTestRule.setContent {
            val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                isRunning = false,
                targetStepsPerSecond = 60.0,
            )

            rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = gameOfLifeAlgorithm,
                clock = testDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            WithDependencies(
                dispatchers = dispatchers,
                gameOfLifeAlgorithm = gameOfLifeAlgorithm,
                composeLifePreferences = preferences,
            ) {
                InteractiveCellUniverse(
                    temporalGameOfLifeState = temporalGameOfLifeState,
                    windowSizeClass = calculateWindowSizeClass(activity = composeTestRule.activity),
                    modifier = Modifier.size(480.dp),
                )
            }
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

    @SkipLeakDetection("appliedChanges", "Outer")
    @Test
    fun six_long_line_evolves_correctly() = runAppTest {
        composeTestRule.setContent {
            val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                targetStepsPerSecond = 60.0,
            )

            rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = gameOfLifeAlgorithm,
                clock = testDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            WithDependencies(
                dispatchers = dispatchers,
                gameOfLifeAlgorithm = gameOfLifeAlgorithm,
                composeLifePreferences = preferences,
            ) {
                InteractiveCellUniverse(
                    temporalGameOfLifeState = temporalGameOfLifeState,
                    windowSizeClass = calculateWindowSizeClass(activity = composeTestRule.activity),
                    modifier = Modifier.fillMaxSize(),
                )
            }
        }

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.pause))
            .performClick()

        SixLongLinePattern.seedCellState.aliveCells.forEach { cell ->
            scrollToCell(cell)

            composeTestRule
                .onNodeWithContentDescription(
                    context.getString(R.string.cell_content_description, cell.x, cell.y),
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

            assertNodesAreAlive(expectedCellState.aliveCells)
        }
    }

    @SkipLeakDetection("appliedChanges", "Outer")
    @Test
    fun six_long_line_evolves_correctly_after_slowing_down() = runAppTest {
        composeTestRule.setContent {
            val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                targetStepsPerSecond = 60.0,
            )

            rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = gameOfLifeAlgorithm,
                clock = testDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            WithDependencies(
                dispatchers = dispatchers,
                gameOfLifeAlgorithm = gameOfLifeAlgorithm,
                composeLifePreferences = preferences,
            ) {
                InteractiveCellUniverse(
                    temporalGameOfLifeState = temporalGameOfLifeState,
                    windowSizeClass = calculateWindowSizeClass(activity = composeTestRule.activity),
                    modifier = Modifier.fillMaxSize(),
                )
            }
        }

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.pause))
            .performClick()

        SixLongLinePattern.seedCellState.aliveCells.forEach { cell ->
            scrollToCell(cell)

            composeTestRule
                .onNodeWithContentDescription(
                    context.getString(R.string.cell_content_description, cell.x, cell.y),
                )
                .performTouchInput { click(topLeft) }
        }

        composeTestRule
            .onNode(
                hasAnyAncestor(hasTestTag("CellUniverseActionCard")) and
                    hasContentDescription(context.getString(R.string.expand)),
            )
            .performClick()

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.target_steps_per_second, 60.0))
            .performSemanticsAction(SemanticsActions.SetProgress) { it(0f) }

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.play))
            .performClick()

        composeTestRule
            .onNode(
                hasAnyAncestor(hasTestTag("CellUniverseActionCard")) and
                    hasContentDescription(context.getString(R.string.collapse)),
            )
            .performClick()

        SixLongLinePattern.cellStates.forEach { expectedCellState ->
            testDispatcher.scheduler.advanceTimeBy(1000)
            testDispatcher.scheduler.runCurrent()
            composeTestRule.waitForIdle()

            assertNodesAreAlive(expectedCellState.aliveCells)
        }
    }

    @SkipLeakDetection("appliedChanges", "Outer")
    @Test
    fun six_long_line_evolves_correctly_with_step() = runAppTest {
        composeTestRule.setContent {
            val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                targetStepsPerSecond = 0.001,
            )

            rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = gameOfLifeAlgorithm,
                clock = testDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            WithDependencies(
                dispatchers = dispatchers,
                gameOfLifeAlgorithm = gameOfLifeAlgorithm,
                composeLifePreferences = preferences,
            ) {
                InteractiveCellUniverse(
                    temporalGameOfLifeState = temporalGameOfLifeState,
                    windowSizeClass = calculateWindowSizeClass(activity = composeTestRule.activity),
                    modifier = Modifier.fillMaxSize(),
                )
            }
        }

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.pause))
            .performClick()

        SixLongLinePattern.seedCellState.aliveCells.forEach { cell ->
            scrollToCell(cell)

            composeTestRule
                .onNodeWithContentDescription(
                    context.getString(R.string.cell_content_description, cell.x, cell.y),
                )
                .performTouchInput { click(topLeft) }
        }

        SixLongLinePattern.cellStates.forEach { expectedCellState ->
            composeTestRule
                .onNodeWithContentDescription(context.getString(R.string.step))
                .performClick()

            testDispatcher.scheduler.runCurrent()
            composeTestRule.waitForIdle()

            assertNodesAreAlive(expectedCellState.aliveCells)
        }
    }

    @SkipLeakDetection("appliedChanges", "Outer")
    @Test
    fun six_long_line_evolves_correctly_with_double_step() = runAppTest {
        composeTestRule.setContent {
            val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                targetStepsPerSecond = 0.001,
            )

            rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = gameOfLifeAlgorithm,
                clock = testDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            WithDependencies(
                dispatchers = dispatchers,
                gameOfLifeAlgorithm = gameOfLifeAlgorithm,
                composeLifePreferences = preferences,
            ) {
                InteractiveCellUniverse(
                    temporalGameOfLifeState = temporalGameOfLifeState,
                    windowSizeClass = calculateWindowSizeClass(activity = composeTestRule.activity),
                    modifier = Modifier.fillMaxSize(),
                )
            }
        }

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.pause))
            .performClick()

        SixLongLinePattern.seedCellState.aliveCells.forEach { cell ->
            scrollToCell(cell)

            composeTestRule
                .onNodeWithContentDescription(
                    context.getString(R.string.cell_content_description, cell.x, cell.y),
                )
                .performTouchInput { click(topLeft) }
        }

        composeTestRule
            .onNode(
                hasAnyAncestor(hasTestTag("CellUniverseActionCard")) and
                    hasContentDescription(context.getString(R.string.expand)),
            )
            .performClick()

        composeTestRule
            .onNodeWithContentDescription(context.getString(R.string.generations_per_step, 1))
            .performSemanticsAction(SemanticsActions.SetProgress) { it(1f) }

        composeTestRule
            .onNode(
                hasAnyAncestor(hasTestTag("CellUniverseActionCard")) and
                    hasContentDescription(context.getString(R.string.collapse)),
            )
            .performClick()

        SixLongLinePattern.cellStates.filterIndexed { index, _ -> index.rem(2) == 1 }.forEach { expectedCellState ->
            composeTestRule
                .onNodeWithContentDescription(context.getString(R.string.step))
                .performClick()

            testDispatcher.scheduler.runCurrent()
            composeTestRule.waitForIdle()

            assertNodesAreAlive(expectedCellState.aliveCells)
        }
    }

    private fun assertNodesAreAlive(cells: Set<IntOffset>) {
        cells.forEach { cell ->
            if (composeTestRule.onAllNodesWithContentDescription(
                    context.getString(R.string.cell_content_description, cell.x, cell.y),
                ).fetchSemanticsNodes().isEmpty()
            ) {
                scrollToCell(cell)
            }

            composeTestRule
                .onNodeWithContentDescription(
                    context.getString(R.string.cell_content_description, cell.x, cell.y),
                )
                .assertIsOn()
        }
    }

    private fun scrollToCell(cell: IntOffset) {
        composeTestRule
            .onNodeWithTag("MutableCellWindow")
            .fetchSemanticsNode()
            .config[ScrollToIndex]
            .action
            ?.invoke(cell.toRingIndex())
    }
}
