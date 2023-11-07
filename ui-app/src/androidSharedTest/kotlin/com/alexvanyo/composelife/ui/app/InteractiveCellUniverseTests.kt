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

package com.alexvanyo.composelife.ui.app

import androidx.compose.foundation.layout.fillMaxSize
import androidx.compose.material3.windowsizeclass.ExperimentalMaterial3WindowSizeClassApi
import androidx.compose.material3.windowsizeclass.calculateWindowSizeClass
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.ui.Modifier
import androidx.compose.ui.input.key.Key
import androidx.compose.ui.semantics.SemanticsActions
import androidx.compose.ui.semantics.SemanticsActions.ScrollToIndex
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.assertIsOn
import androidx.compose.ui.test.click
import androidx.compose.ui.test.hasAnyAncestor
import androidx.compose.ui.test.hasContentDescription
import androidx.compose.ui.test.hasImeAction
import androidx.compose.ui.test.hasSetTextAction
import androidx.compose.ui.test.hasTestTag
import androidx.compose.ui.test.hasText
import androidx.compose.ui.test.onAllNodesWithContentDescription
import androidx.compose.ui.test.onChild
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.onNodeWithTag
import androidx.compose.ui.test.onRoot
import androidx.compose.ui.test.performClick
import androidx.compose.ui.test.performImeAction
import androidx.compose.ui.test.performKeyInput
import androidx.compose.ui.test.performSemanticsAction
import androidx.compose.ui.test.performTextReplacement
import androidx.compose.ui.test.performTouchInput
import androidx.compose.ui.test.pressKey
import androidx.compose.ui.text.input.ImeAction
import androidx.compose.ui.unit.IntOffset
import androidx.test.espresso.Espresso
import com.alexvanyo.composelife.dispatchers.clock
import com.alexvanyo.composelife.geometry.toRingIndex
import com.alexvanyo.composelife.kmpandroidrunner.KmpAndroidJUnit4
import com.alexvanyo.composelife.model.rememberTemporalGameOfLifeState
import com.alexvanyo.composelife.model.rememberTemporalGameOfLifeStateMutator
import com.alexvanyo.composelife.patterns.SixLongLinePattern
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferences
import com.alexvanyo.composelife.test.BaseUiInjectTest
import com.alexvanyo.composelife.test.InjectTestActivity
import com.alexvanyo.composelife.ui.util.ClipboardState
import com.alexvanyo.composelife.ui.util.rememberClipboardState
import kotlinx.coroutines.ExperimentalCoroutinesApi
import leakcanary.SkipLeakDetection
import org.junit.runner.RunWith
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull

@OptIn(ExperimentalCoroutinesApi::class, ExperimentalMaterial3WindowSizeClassApi::class)
@RunWith(KmpAndroidJUnit4::class)
class InteractiveCellUniverseTests : BaseUiInjectTest<TestComposeLifeApplicationComponent, InjectTestActivity>(
    { TestComposeLifeApplicationComponent.create() },
    InjectTestActivity::class.java,
) {
    private val testDispatcher get() = applicationComponent.testDispatcher

    private val gameOfLifeAlgorithm get() = applicationComponent.gameOfLifeAlgorithm

    private val dispatchers get() = applicationComponent.dispatchers

    private val interactiveCellUniverseInjectEntryPoint get() =
        composeTestRule.activity.uiComponent.entryPoint as InteractiveCellUniverseInjectEntryPoint

    private val interactiveCellUniverseLocalEntryPoint = object : InteractiveCellUniverseLocalEntryPoint {
        override val preferences = LoadedComposeLifePreferences.Defaults
    }

    @SkipLeakDetection("appliedChanges", "Outer")
    @Test
    fun info_card_closes_upon_back_press() = runAppTest {
        composeTestRule.setContent {
            val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                isRunning = false,
                targetStepsPerSecond = 60.0,
            )

            val temporalGameOfLifeStateMutator = rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = gameOfLifeAlgorithm,
                clock = testDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            LaunchedEffect(temporalGameOfLifeStateMutator) {
                temporalGameOfLifeStateMutator.update()
            }

            with(interactiveCellUniverseInjectEntryPoint) {
                with(interactiveCellUniverseLocalEntryPoint) {
                    InteractiveCellUniverse(
                        temporalGameOfLifeState = temporalGameOfLifeState,
                        windowSizeClass = calculateWindowSizeClass(activity = composeTestRule.activity),
                        modifier = Modifier.fillMaxSize(),
                    )
                }
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

            val temporalGameOfLifeStateMutator = rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = gameOfLifeAlgorithm,
                clock = testDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            LaunchedEffect(temporalGameOfLifeStateMutator) {
                temporalGameOfLifeStateMutator.update()
            }

            with(interactiveCellUniverseInjectEntryPoint) {
                with(interactiveCellUniverseLocalEntryPoint) {
                    InteractiveCellUniverse(
                        temporalGameOfLifeState = temporalGameOfLifeState,
                        windowSizeClass = calculateWindowSizeClass(activity = composeTestRule.activity),
                        modifier = Modifier.fillMaxSize(),
                    )
                }
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

            val temporalGameOfLifeStateMutator = rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = gameOfLifeAlgorithm,
                clock = testDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            LaunchedEffect(temporalGameOfLifeStateMutator) {
                temporalGameOfLifeStateMutator.update()
            }

            with(interactiveCellUniverseInjectEntryPoint) {
                with(interactiveCellUniverseLocalEntryPoint) {
                    InteractiveCellUniverse(
                        temporalGameOfLifeState = temporalGameOfLifeState,
                        windowSizeClass = calculateWindowSizeClass(activity = composeTestRule.activity),
                        modifier = Modifier.fillMaxSize(),
                    )
                }
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
            testDispatcher.scheduler.runCurrent()
            composeTestRule.waitForIdle()
            testDispatcher.scheduler.advanceTimeBy(16)
            testDispatcher.scheduler.runCurrent()
            composeTestRule.waitForIdle()

            assertNodesAreAlive(expectedCellState.aliveCells)
        }
    }

    @OptIn(ExperimentalTestApi::class)
    @SkipLeakDetection("appliedChanges", "Outer")
    @Test
    fun six_long_line_evolves_correctly_with_spacebar() = runAppTest {
        composeTestRule.setContent {
            val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                targetStepsPerSecond = 60.0,
            )

            val temporalGameOfLifeStateMutator = rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = gameOfLifeAlgorithm,
                clock = testDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            LaunchedEffect(temporalGameOfLifeStateMutator) {
                temporalGameOfLifeStateMutator.update()
            }

            with(interactiveCellUniverseInjectEntryPoint) {
                with(interactiveCellUniverseLocalEntryPoint) {
                    InteractiveCellUniverse(
                        temporalGameOfLifeState = temporalGameOfLifeState,
                        windowSizeClass = calculateWindowSizeClass(activity = composeTestRule.activity),
                        modifier = Modifier.fillMaxSize(),
                    )
                }
            }
        }

        composeTestRule
            .onRoot()
            .performKeyInput {
                pressKey(Key.Spacebar)
            }

        SixLongLinePattern.seedCellState.aliveCells.forEach { cell ->
            scrollToCell(cell)

            composeTestRule
                .onNodeWithContentDescription(
                    context.getString(R.string.cell_content_description, cell.x, cell.y),
                )
                .performTouchInput { click(topLeft) }
        }

        composeTestRule
            .onRoot()
            .performKeyInput {
                pressKey(Key.Spacebar)
            }

        SixLongLinePattern.cellStates.forEach { expectedCellState ->
            testDispatcher.scheduler.runCurrent()
            composeTestRule.waitForIdle()
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

            val temporalGameOfLifeStateMutator = rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = gameOfLifeAlgorithm,
                clock = testDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            LaunchedEffect(temporalGameOfLifeStateMutator) {
                temporalGameOfLifeStateMutator.update()
            }

            with(interactiveCellUniverseInjectEntryPoint) {
                with(interactiveCellUniverseLocalEntryPoint) {
                    InteractiveCellUniverse(
                        temporalGameOfLifeState = temporalGameOfLifeState,
                        windowSizeClass = calculateWindowSizeClass(activity = composeTestRule.activity),
                        modifier = Modifier.fillMaxSize(),
                    )
                }
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
            .onNodeWithContentDescription(context.getString(R.string.target_steps_per_second_label_and_value, 60.0))
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
            testDispatcher.scheduler.runCurrent()
            composeTestRule.waitForIdle()
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

            val temporalGameOfLifeStateMutator = rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = gameOfLifeAlgorithm,
                clock = testDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            LaunchedEffect(temporalGameOfLifeStateMutator) {
                temporalGameOfLifeStateMutator.update()
            }

            with(interactiveCellUniverseInjectEntryPoint) {
                with(interactiveCellUniverseLocalEntryPoint) {
                    InteractiveCellUniverse(
                        temporalGameOfLifeState = temporalGameOfLifeState,
                        windowSizeClass = calculateWindowSizeClass(activity = composeTestRule.activity),
                        modifier = Modifier.fillMaxSize(),
                    )
                }
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
            testDispatcher.scheduler.runCurrent()
            composeTestRule.waitForIdle()

            assertNodesAreAlive(expectedCellState.aliveCells)
        }
    }

    @SkipLeakDetection("appliedChanges", "Outer")
    @Test
    fun six_long_line_evolves_correctly_with_double_step_via_slider() = runAppTest {
        composeTestRule.setContent {
            val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                targetStepsPerSecond = 0.001,
            )

            val temporalGameOfLifeStateMutator = rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = gameOfLifeAlgorithm,
                clock = testDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            LaunchedEffect(temporalGameOfLifeStateMutator) {
                temporalGameOfLifeStateMutator.update()
            }

            with(interactiveCellUniverseInjectEntryPoint) {
                with(interactiveCellUniverseLocalEntryPoint) {
                    InteractiveCellUniverse(
                        temporalGameOfLifeState = temporalGameOfLifeState,
                        windowSizeClass = calculateWindowSizeClass(activity = composeTestRule.activity),
                        modifier = Modifier.fillMaxSize(),
                    )
                }
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
            .onNodeWithContentDescription(context.getString(R.string.generations_per_step_label_and_value, 1))
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
            testDispatcher.scheduler.runCurrent()
            composeTestRule.waitForIdle()

            assertNodesAreAlive(expectedCellState.aliveCells)
        }
    }

    @SkipLeakDetection("appliedChanges", "Outer")
    @Test
    fun six_long_line_evolves_correctly_with_double_step_via_text() = runAppTest {
        composeTestRule.setContent {
            val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                targetStepsPerSecond = 0.001,
            )

            val temporalGameOfLifeStateMutator = rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = gameOfLifeAlgorithm,
                clock = testDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            LaunchedEffect(temporalGameOfLifeStateMutator) {
                temporalGameOfLifeStateMutator.update()
            }

            with(interactiveCellUniverseInjectEntryPoint) {
                with(interactiveCellUniverseLocalEntryPoint) {
                    InteractiveCellUniverse(
                        temporalGameOfLifeState = temporalGameOfLifeState,
                        windowSizeClass = calculateWindowSizeClass(activity = composeTestRule.activity),
                        modifier = Modifier.fillMaxSize(),
                    )
                }
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
            .onNode(
                hasSetTextAction() and hasImeAction(ImeAction.Done) and
                    hasText(context.getString(R.string.generations_per_step_label)),
            )
            .performTextReplacement("2")
        composeTestRule
            .onNode(
                hasSetTextAction() and hasImeAction(ImeAction.Done) and
                    hasText(context.getString(R.string.generations_per_step_label)),
            )
            .performImeAction()

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
            testDispatcher.scheduler.runCurrent()
            composeTestRule.waitForIdle()

            assertNodesAreAlive(expectedCellState.aliveCells)
        }
    }

    @OptIn(ExperimentalTestApi::class)
    @SkipLeakDetection("appliedChanges", "Outer")
    @Test
    fun glider_is_copied_correctly_with_keyboard_shortcuts() = runAppTest {
        lateinit var clipboardState: ClipboardState

        composeTestRule.setContent {
            clipboardState = rememberClipboardState()

            val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                targetStepsPerSecond = 60.0,
            )

            val temporalGameOfLifeStateMutator = rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = gameOfLifeAlgorithm,
                clock = testDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            LaunchedEffect(temporalGameOfLifeStateMutator) {
                temporalGameOfLifeStateMutator.update()
            }

            with(interactiveCellUniverseInjectEntryPoint) {
                with(interactiveCellUniverseLocalEntryPoint) {
                    InteractiveCellUniverse(
                        temporalGameOfLifeState = temporalGameOfLifeState,
                        windowSizeClass = calculateWindowSizeClass(activity = composeTestRule.activity),
                        modifier = Modifier.fillMaxSize(),
                    )
                }
            }
        }

        composeTestRule
            .onRoot()
            .performKeyInput {
                pressKey(Key.Spacebar)
            }

        listOf(
            IntOffset(1, 0),
            IntOffset(2, 1),
            IntOffset(0, 2),
            IntOffset(1, 2),
            IntOffset(2, 2),
        ).forEach { cell ->
            scrollToCell(cell)

            composeTestRule
                .onNodeWithContentDescription(
                    context.getString(R.string.cell_content_description, cell.x, cell.y),
                )
                .performTouchInput { click(topLeft) }
        }

        composeTestRule
            .onRoot()
            .performKeyInput {
                keyDown(Key.CtrlLeft)
                pressKey(Key.A)
                keyUp(Key.CtrlLeft)
            }

        composeTestRule
            .onRoot()
            .performKeyInput {
                keyDown(Key.CtrlLeft)
                pressKey(Key.C)
                keyUp(Key.CtrlLeft)
            }

        val clipData = clipboardState.clipData
        assertNotNull(clipData)
        assertEquals(
            """
                #R 0 0
                x = 3, y = 3, rule = B3/S23
                bo$2bo$3o!
            """.trimIndent(),
            clipData.getItemAt(0).text,
        )
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
            .onChild()
            .fetchSemanticsNode()
            .config[ScrollToIndex]
            .action
            ?.invoke(cell.toRingIndex())
    }
}
