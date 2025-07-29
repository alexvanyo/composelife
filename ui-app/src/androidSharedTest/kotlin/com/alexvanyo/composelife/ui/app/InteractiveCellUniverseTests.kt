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
import androidx.compose.material3.adaptive.currentWindowAdaptiveInfo
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.input.key.Key
import androidx.compose.ui.semantics.SemanticsActions
import androidx.compose.ui.test.ComposeUiTest
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.assertIsOn
import androidx.compose.ui.test.click
import androidx.compose.ui.test.filterToOne
import androidx.compose.ui.test.hasAnyAncestor
import androidx.compose.ui.test.hasContentDescription
import androidx.compose.ui.test.hasImeAction
import androidx.compose.ui.test.hasScrollToIndexAction
import androidx.compose.ui.test.hasSetTextAction
import androidx.compose.ui.test.hasTestTag
import androidx.compose.ui.test.hasText
import androidx.compose.ui.test.onAllNodesWithContentDescription
import androidx.compose.ui.test.onChildren
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.onNodeWithTag
import androidx.compose.ui.test.onRoot
import androidx.compose.ui.test.performClick
import androidx.compose.ui.test.performImeAction
import androidx.compose.ui.test.performKeyInput
import androidx.compose.ui.test.performScrollToIndex
import androidx.compose.ui.test.performSemanticsAction
import androidx.compose.ui.test.performTextReplacement
import androidx.compose.ui.test.performTouchInput
import androidx.compose.ui.test.pressKey
import androidx.compose.ui.text.input.ImeAction
import androidx.compose.ui.unit.IntOffset
import androidx.test.espresso.Espresso
import com.alexvanyo.composelife.algorithm.GameOfLifeAlgorithm
import com.alexvanyo.composelife.dispatchers.CellTickerTestDispatcher
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.dispatchers.GeneralTestDispatcher
import com.alexvanyo.composelife.dispatchers.clock
import com.alexvanyo.composelife.geometry.toRingIndex
import com.alexvanyo.composelife.model.rememberTemporalGameOfLifeState
import com.alexvanyo.composelife.model.rememberTemporalGameOfLifeStateMutator
import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResolver
import com.alexvanyo.composelife.patterns.SixLongLinePattern
import com.alexvanyo.composelife.scopes.ApplicationGraph
import com.alexvanyo.composelife.scopes.UiGraph
import com.alexvanyo.composelife.scopes.UiScope
import com.alexvanyo.composelife.test.BaseUiInjectTest
import com.alexvanyo.composelife.test.runUiTest
import com.alexvanyo.composelife.ui.app.resources.ApplyPaste
import com.alexvanyo.composelife.ui.app.resources.Collapse
import com.alexvanyo.composelife.ui.app.resources.Copy
import com.alexvanyo.composelife.ui.app.resources.Expand
import com.alexvanyo.composelife.ui.app.resources.GenerationsPerStepLabel
import com.alexvanyo.composelife.ui.app.resources.GenerationsPerStepLabelAndValue
import com.alexvanyo.composelife.ui.app.resources.Pause
import com.alexvanyo.composelife.ui.app.resources.Play
import com.alexvanyo.composelife.ui.app.resources.Step
import com.alexvanyo.composelife.ui.app.resources.Strings
import com.alexvanyo.composelife.ui.app.resources.TargetStepsPerSecondLabelAndValue
import com.alexvanyo.composelife.ui.cells.rememberMutableCellWindowViewportState
import com.alexvanyo.composelife.ui.cells.resources.InteractableCellContentDescription
import com.alexvanyo.composelife.ui.util.ClipboardReaderWriter
import com.alexvanyo.composelife.ui.util.rememberFakeClipboardReaderWriter
import com.alexvanyo.composelife.ui.util.setText
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.asContribution
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.test.TestDispatcher
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertNotNull
import kotlin.time.Duration.Companion.seconds
import com.alexvanyo.composelife.ui.cells.resources.Strings as CellsStrings

@ContributesTo(AppScope::class)
interface InteractiveCellUniverseTestsAppEntryPoint {
    @GeneralTestDispatcher val generalTestDispatcher: TestDispatcher

    @CellTickerTestDispatcher val cellTickerTestDispatcher: TestDispatcher
    val gameOfLifeAlgorithm: GameOfLifeAlgorithm
    val dispatchers: ComposeLifeDispatchers
}

// TODO: Replace with asContribution()
val ApplicationGraph.interactiveCellUniverseTestsAppEntryPoint: InteractiveCellUniverseTestsAppEntryPoint get() =
    this as InteractiveCellUniverseTestsAppEntryPoint

@ContributesTo(UiScope::class)
interface InteractiveCellUniverseTestsUiEntryPoint {
    val interactiveCellUniverseEntryPoint: InteractiveCellUniverseEntryPoint
}

// TODO: Replace with asContribution()
val UiGraph.interactiveCellUniverseTestsUiEntryPoint: InteractiveCellUniverseTestsUiEntryPoint get() =
    this as InteractiveCellUniverseTestsUiEntryPoint

@Suppress("LargeClass")
@OptIn(ExperimentalCoroutinesApi::class, ExperimentalTestApi::class)
class InteractiveCellUniverseTests : BaseUiInjectTest(
    { globalGraph.asContribution<ApplicationGraph.Factory>().create(it) },
) {
    private val entryPoint get() = applicationGraph.interactiveCellUniverseTestsAppEntryPoint

    private val generalTestDispatcher get() = entryPoint.generalTestDispatcher

    private val cellTickerTestDispatcher get() = entryPoint.cellTickerTestDispatcher

    private val gameOfLifeAlgorithm get() = entryPoint.gameOfLifeAlgorithm

    private val dispatchers get() = entryPoint.dispatchers

    @Test
    fun info_card_closes_upon_back_press() = runUiTest(generalTestDispatcher) { uiGraph ->
        val uiEntryPoint = uiGraph.interactiveCellUniverseTestsUiEntryPoint

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                isRunning = false,
                targetStepsPerSecond = 60.0,
            )

            val temporalGameOfLifeStateMutator = rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = gameOfLifeAlgorithm,
                clock = cellTickerTestDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            LaunchedEffect(temporalGameOfLifeStateMutator) {
                temporalGameOfLifeStateMutator.update()
            }

            with(uiEntryPoint.interactiveCellUniverseEntryPoint) {
                InteractiveCellUniverse(
                    temporalGameOfLifeState = temporalGameOfLifeState,
                    windowSizeClass = currentWindowAdaptiveInfo().windowSizeClass,
                    onSeeMoreSettingsClicked = {},
                    onOpenInSettingsClicked = {},
                    onViewDeserializationInfo = {},
                    modifier = Modifier.fillMaxSize(),
                )
            }
        }

        onNode(
            hasAnyAncestor(hasTestTag("CellUniverseActionCard")) and
                hasContentDescription(resolver.invoke(Strings.Expand)),
        )
            .performClick()

        generalTestDispatcher.scheduler.advanceUntilIdle()
        waitForIdle()

        Espresso.pressBack()

        onNodeWithContentDescription(resolver.invoke(Strings.Collapse))
            .assertDoesNotExist()
    }

    @Test
    fun action_card_closes_upon_back_press() = runUiTest(generalTestDispatcher) { uiGraph ->
        val uiEntryPoint = uiGraph.interactiveCellUniverseTestsUiEntryPoint

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                isRunning = false,
                targetStepsPerSecond = 60.0,
            )

            val temporalGameOfLifeStateMutator = rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = gameOfLifeAlgorithm,
                clock = cellTickerTestDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            LaunchedEffect(temporalGameOfLifeStateMutator) {
                temporalGameOfLifeStateMutator.update()
            }

            with(uiEntryPoint.interactiveCellUniverseEntryPoint) {
                InteractiveCellUniverse(
                    temporalGameOfLifeState = temporalGameOfLifeState,
                    windowSizeClass = currentWindowAdaptiveInfo().windowSizeClass,
                    onSeeMoreSettingsClicked = {},
                    onOpenInSettingsClicked = {},
                    onViewDeserializationInfo = {},
                    modifier = Modifier.fillMaxSize(),
                )
            }
        }

        onNode(
            hasAnyAncestor(hasTestTag("CellUniverseActionCard")) and
                hasContentDescription(resolver.invoke(Strings.Expand)),
        )
            .performClick()

        generalTestDispatcher.scheduler.advanceUntilIdle()
        waitForIdle()

        Espresso.pressBack()

        onNodeWithContentDescription(resolver.invoke(Strings.Collapse))
            .assertDoesNotExist()
    }

    @Test
    fun six_long_line_evolves_correctly() = runUiTest(
        generalTestDispatcher,
        120.seconds,
    ) { uiGraph ->
        val uiEntryPoint = uiGraph.interactiveCellUniverseTestsUiEntryPoint

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                targetStepsPerSecond = 60.0,
            )

            val temporalGameOfLifeStateMutator = rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = gameOfLifeAlgorithm,
                clock = cellTickerTestDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            LaunchedEffect(temporalGameOfLifeStateMutator) {
                temporalGameOfLifeStateMutator.update()
            }

            with(uiEntryPoint.interactiveCellUniverseEntryPoint) {
                InteractiveCellUniverse(
                    temporalGameOfLifeState = temporalGameOfLifeState,
                    windowSizeClass = currentWindowAdaptiveInfo().windowSizeClass,
                    onSeeMoreSettingsClicked = {},
                    onOpenInSettingsClicked = {},
                    onViewDeserializationInfo = {},
                    modifier = Modifier.fillMaxSize(),
                )
            }
        }

        onNodeWithContentDescription(resolver.invoke(Strings.Pause))
            .performClick()

        SixLongLinePattern.seedCellState.aliveCells.forEach { cell ->
            scrollToCell(cell)

            onNodeWithContentDescription(
                resolver.invoke(CellsStrings.InteractableCellContentDescription(cell.x, cell.y)),
            )
                .performTouchInput { click(topLeft) }
        }

        onNodeWithContentDescription(resolver.invoke(Strings.Play))
            .performClick()

        SixLongLinePattern.cellStates.forEach { expectedCellState ->
            generalTestDispatcher.scheduler.advanceUntilIdle()
            waitForIdle()
            cellTickerTestDispatcher.scheduler.advanceTimeBy(17)
            cellTickerTestDispatcher.scheduler.runCurrent()
            generalTestDispatcher.scheduler.advanceUntilIdle()
            waitForIdle()

            assertNodesAreAlive(resolver, expectedCellState.aliveCells)
        }
    }

    @Test
    fun six_long_line_evolves_correctly_with_spacebar() = runUiTest(
        generalTestDispatcher,
        120.seconds,
    ) { uiGraph ->
        val uiEntryPoint = uiGraph.interactiveCellUniverseTestsUiEntryPoint

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                targetStepsPerSecond = 60.0,
            )

            val temporalGameOfLifeStateMutator = rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = gameOfLifeAlgorithm,
                clock = cellTickerTestDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            LaunchedEffect(temporalGameOfLifeStateMutator) {
                temporalGameOfLifeStateMutator.update()
            }

            with(uiEntryPoint.interactiveCellUniverseEntryPoint) {
                InteractiveCellUniverse(
                    temporalGameOfLifeState = temporalGameOfLifeState,
                    windowSizeClass = currentWindowAdaptiveInfo().windowSizeClass,
                    onSeeMoreSettingsClicked = {},
                    onOpenInSettingsClicked = {},
                    onViewDeserializationInfo = {},
                    modifier = Modifier.fillMaxSize(),
                )
            }
        }

        onRoot()
            .performKeyInput {
                pressKey(Key.Spacebar)
            }

        SixLongLinePattern.seedCellState.aliveCells.forEach { cell ->
            scrollToCell(cell)

            onNodeWithContentDescription(
                resolver.invoke(CellsStrings.InteractableCellContentDescription(cell.x, cell.y)),
            )
                .performTouchInput { click(topLeft) }
        }

        onRoot()
            .performKeyInput {
                pressKey(Key.Spacebar)
            }

        SixLongLinePattern.cellStates.forEach { expectedCellState ->
            generalTestDispatcher.scheduler.advanceUntilIdle()
            waitForIdle()
            cellTickerTestDispatcher.scheduler.advanceTimeBy(17)
            cellTickerTestDispatcher.scheduler.runCurrent()
            generalTestDispatcher.scheduler.advanceUntilIdle()
            waitForIdle()

            assertNodesAreAlive(resolver, expectedCellState.aliveCells)
        }
    }

    @Test
    fun six_long_line_evolves_correctly_after_slowing_down() = runUiTest(
        generalTestDispatcher,
        120.seconds,
    ) { uiGraph ->
        val uiEntryPoint = uiGraph.interactiveCellUniverseTestsUiEntryPoint

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                targetStepsPerSecond = 60.0,
            )

            val temporalGameOfLifeStateMutator = rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = gameOfLifeAlgorithm,
                clock = cellTickerTestDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            LaunchedEffect(temporalGameOfLifeStateMutator) {
                temporalGameOfLifeStateMutator.update()
            }

            with(uiEntryPoint.interactiveCellUniverseEntryPoint) {
                InteractiveCellUniverse(
                    temporalGameOfLifeState = temporalGameOfLifeState,
                    windowSizeClass = currentWindowAdaptiveInfo().windowSizeClass,
                    onSeeMoreSettingsClicked = {},
                    onOpenInSettingsClicked = {},
                    onViewDeserializationInfo = {},
                    modifier = Modifier.fillMaxSize(),
                )
            }
        }

        onNodeWithContentDescription(resolver.invoke(Strings.Pause))
            .performClick()

        SixLongLinePattern.seedCellState.aliveCells.forEach { cell ->
            scrollToCell(cell)

            onNodeWithContentDescription(
                resolver.invoke(CellsStrings.InteractableCellContentDescription(cell.x, cell.y)),
            )
                .performTouchInput { click(topLeft) }
        }

        onNode(
            hasAnyAncestor(hasTestTag("CellUniverseActionCard")) and
                hasContentDescription(resolver.invoke(Strings.Expand)),
        )
            .performClick()

        onNodeWithContentDescription(resolver.invoke(Strings.TargetStepsPerSecondLabelAndValue(60.0)))
            .performSemanticsAction(SemanticsActions.SetProgress) { it(0f) }

        onNodeWithContentDescription(resolver.invoke(Strings.Play))
            .performClick()

        onNode(
            hasAnyAncestor(hasTestTag("CellUniverseActionCard")) and
                hasContentDescription(resolver.invoke(Strings.Collapse)),
        )
            .performClick()

        SixLongLinePattern.cellStates.forEach { expectedCellState ->
            generalTestDispatcher.scheduler.advanceUntilIdle()
            waitForIdle()
            cellTickerTestDispatcher.scheduler.advanceTimeBy(1000)
            cellTickerTestDispatcher.scheduler.runCurrent()
            generalTestDispatcher.scheduler.advanceUntilIdle()
            waitForIdle()

            assertNodesAreAlive(resolver, expectedCellState.aliveCells)
        }
    }

    @Test
    fun six_long_line_evolves_correctly_with_step() = runUiTest(
        generalTestDispatcher,
        120.seconds,
    ) { uiGraph ->
        val uiEntryPoint = uiGraph.interactiveCellUniverseTestsUiEntryPoint

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                targetStepsPerSecond = 0.001,
            )

            val temporalGameOfLifeStateMutator = rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = gameOfLifeAlgorithm,
                clock = cellTickerTestDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            LaunchedEffect(temporalGameOfLifeStateMutator) {
                temporalGameOfLifeStateMutator.update()
            }

            with(uiEntryPoint.interactiveCellUniverseEntryPoint) {
                InteractiveCellUniverse(
                    temporalGameOfLifeState = temporalGameOfLifeState,
                    windowSizeClass = currentWindowAdaptiveInfo().windowSizeClass,
                    onSeeMoreSettingsClicked = {},
                    onOpenInSettingsClicked = {},
                    onViewDeserializationInfo = {},
                    modifier = Modifier.fillMaxSize(),
                )
            }
        }

        onNodeWithContentDescription(resolver.invoke(Strings.Pause))
            .performClick()

        SixLongLinePattern.seedCellState.aliveCells.forEach { cell ->
            scrollToCell(cell)

            onNodeWithContentDescription(
                resolver.invoke(CellsStrings.InteractableCellContentDescription(cell.x, cell.y)),
            )
                .performTouchInput { click(topLeft) }
        }

        SixLongLinePattern.cellStates.forEach { expectedCellState ->
            onNodeWithContentDescription(resolver.invoke(Strings.Step))
                .performClick()

            generalTestDispatcher.scheduler.advanceUntilIdle()
            waitForIdle()

            assertNodesAreAlive(resolver, expectedCellState.aliveCells)
        }
    }

    @Test
    fun six_long_line_evolves_correctly_with_double_step_via_slider() = runUiTest(
        generalTestDispatcher,
        120.seconds,
    ) { uiGraph ->
        val uiEntryPoint = uiGraph.interactiveCellUniverseTestsUiEntryPoint

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                targetStepsPerSecond = 0.001,
            )

            val temporalGameOfLifeStateMutator = rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = gameOfLifeAlgorithm,
                clock = cellTickerTestDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            LaunchedEffect(temporalGameOfLifeStateMutator) {
                temporalGameOfLifeStateMutator.update()
            }
            with(uiEntryPoint.interactiveCellUniverseEntryPoint) {
                InteractiveCellUniverse(
                    temporalGameOfLifeState = temporalGameOfLifeState,
                    windowSizeClass = currentWindowAdaptiveInfo().windowSizeClass,
                    onSeeMoreSettingsClicked = {},
                    onOpenInSettingsClicked = {},
                    onViewDeserializationInfo = {},
                    modifier = Modifier.fillMaxSize(),
                )
            }
        }

        onNodeWithContentDescription(resolver.invoke(Strings.Pause))
            .performClick()

        SixLongLinePattern.seedCellState.aliveCells.forEach { cell ->
            scrollToCell(cell)

            onNodeWithContentDescription(
                resolver.invoke(CellsStrings.InteractableCellContentDescription(cell.x, cell.y)),
            )
                .performTouchInput { click(topLeft) }
        }

        onNode(
            hasAnyAncestor(hasTestTag("CellUniverseActionCard")) and
                hasContentDescription(resolver.invoke(Strings.Expand)),
        )
            .performClick()

        onNodeWithContentDescription(resolver.invoke(Strings.GenerationsPerStepLabelAndValue(1)))
            .performSemanticsAction(SemanticsActions.SetProgress) { it(1f) }

        onNode(
            hasAnyAncestor(hasTestTag("CellUniverseActionCard")) and
                hasContentDescription(resolver.invoke(Strings.Collapse)),
        )
            .performClick()

        SixLongLinePattern.cellStates.filterIndexed { index, _ -> index.rem(2) == 1 }.forEach { expectedCellState ->
            onNodeWithContentDescription(resolver.invoke(Strings.Step))
                .performClick()

            generalTestDispatcher.scheduler.advanceUntilIdle()
            waitForIdle()

            assertNodesAreAlive(resolver, expectedCellState.aliveCells)
        }
    }

    @Test
    fun six_long_line_evolves_correctly_with_double_step_via_text() = runUiTest(
        generalTestDispatcher,
        120.seconds,
    ) { uiGraph ->
        val uiEntryPoint = uiGraph.interactiveCellUniverseTestsUiEntryPoint

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                targetStepsPerSecond = 0.001,
            )

            val temporalGameOfLifeStateMutator = rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = gameOfLifeAlgorithm,
                clock = cellTickerTestDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            LaunchedEffect(temporalGameOfLifeStateMutator) {
                temporalGameOfLifeStateMutator.update()
            }
            with(uiEntryPoint.interactiveCellUniverseEntryPoint) {
                InteractiveCellUniverse(
                    temporalGameOfLifeState = temporalGameOfLifeState,
                    windowSizeClass = currentWindowAdaptiveInfo().windowSizeClass,
                    onSeeMoreSettingsClicked = {},
                    onOpenInSettingsClicked = {},
                    onViewDeserializationInfo = {},
                    modifier = Modifier.fillMaxSize(),
                )
            }
        }

        onNodeWithContentDescription(resolver.invoke(Strings.Pause))
            .performClick()

        SixLongLinePattern.seedCellState.aliveCells.forEach { cell ->
            scrollToCell(cell)

            onNodeWithContentDescription(
                resolver.invoke(CellsStrings.InteractableCellContentDescription(cell.x, cell.y)),
            )
                .performTouchInput { click(topLeft) }
        }

        onNode(
            hasAnyAncestor(hasTestTag("CellUniverseActionCard")) and
                hasContentDescription(resolver.invoke(Strings.Expand)),
        )
            .performClick()

        onNode(
            hasSetTextAction() and hasImeAction(ImeAction.Done) and
                hasText(resolver.invoke(Strings.GenerationsPerStepLabel)),
        )
            .performTextReplacement("2")
        onNode(
            hasSetTextAction() and hasImeAction(ImeAction.Done) and
                hasText(resolver.invoke(Strings.GenerationsPerStepLabel)),
        )
            .performImeAction()

        onNode(
            hasAnyAncestor(hasTestTag("CellUniverseActionCard")) and
                hasContentDescription(resolver.invoke(Strings.Collapse)),
        )
            .performClick()

        SixLongLinePattern.cellStates.filterIndexed { index, _ -> index.rem(2) == 1 }.forEach { expectedCellState ->
            onNodeWithContentDescription(resolver.invoke(Strings.Step))
                .performClick()

            generalTestDispatcher.scheduler.advanceUntilIdle()
            waitForIdle()

            assertNodesAreAlive(resolver, expectedCellState.aliveCells)
        }
    }

    @Test
    fun glider_is_copied_correctly_with_keyboard_shortcuts() = runUiTest(
        generalTestDispatcher,
    ) { uiGraph ->
        val uiEntryPoint = uiGraph.interactiveCellUniverseTestsUiEntryPoint

        lateinit var clipboardReaderWriter: ClipboardReaderWriter
        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                targetStepsPerSecond = 60.0,
            )

            val temporalGameOfLifeStateMutator = rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = gameOfLifeAlgorithm,
                clock = cellTickerTestDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            LaunchedEffect(temporalGameOfLifeStateMutator) {
                temporalGameOfLifeStateMutator.update()
            }
            with(uiEntryPoint.interactiveCellUniverseEntryPoint) {
                clipboardReaderWriter = rememberFakeClipboardReaderWriter()

                InteractiveCellUniverse(
                    temporalGameOfLifeState = temporalGameOfLifeState,
                    windowSizeClass = currentWindowAdaptiveInfo().windowSizeClass,
                    onSeeMoreSettingsClicked = {},
                    onOpenInSettingsClicked = {},
                    onViewDeserializationInfo = {},
                    modifier = Modifier.fillMaxSize(),
                    interactiveCellUniverseState = rememberInteractiveCellUniverseState(
                        temporalGameOfLifeState = temporalGameOfLifeState,
                        clipboardReaderWriter = clipboardReaderWriter,
                    ),
                )
            }
        }

        onRoot()
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

            onNodeWithContentDescription(
                resolver.invoke(CellsStrings.InteractableCellContentDescription(cell.x, cell.y)),
            )
                .performTouchInput { click(topLeft) }
        }

        onRoot()
            .performKeyInput {
                keyDown(Key.CtrlLeft)
                pressKey(Key.A)
                keyUp(Key.CtrlLeft)
            }

        onRoot()
            .performKeyInput {
                keyDown(Key.CtrlLeft)
                keyDown(Key.C)
            }

        val clipData = clipboardReaderWriter.getClipData()
        assertNotNull(clipData)
        assertEquals(
            """
                #R 0 0
                x = 3, y = 3, rule = B3/S23
                bo$2bo$3o!
            """.trimIndent(),
            clipData.getItemAt(0).text,
        )

        onRoot()
            .performKeyInput {
                keyUp(Key.CtrlLeft)
                keyUp(Key.C)
            }
    }

    @Test
    fun selection_is_cleared_correctly_with_keyboard_shortcuts() = runUiTest(
        generalTestDispatcher,
    ) { uiGraph ->
        val uiEntryPoint = uiGraph.interactiveCellUniverseTestsUiEntryPoint

        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                targetStepsPerSecond = 60.0,
            )

            val temporalGameOfLifeStateMutator = rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = gameOfLifeAlgorithm,
                clock = cellTickerTestDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            LaunchedEffect(temporalGameOfLifeStateMutator) {
                temporalGameOfLifeStateMutator.update()
            }

            with(uiEntryPoint.interactiveCellUniverseEntryPoint) {
                InteractiveCellUniverse(
                    temporalGameOfLifeState = temporalGameOfLifeState,
                    windowSizeClass = currentWindowAdaptiveInfo().windowSizeClass,
                    onSeeMoreSettingsClicked = {},
                    onOpenInSettingsClicked = {},
                    onViewDeserializationInfo = {},
                    modifier = Modifier.fillMaxSize(),
                )
            }
        }

        onRoot()
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

            onNodeWithContentDescription(
                resolver.invoke(CellsStrings.InteractableCellContentDescription(cell.x, cell.y)),
            )
                .performTouchInput { click(topLeft) }
        }

        onRoot()
            .performKeyInput {
                keyDown(Key.CtrlLeft)
                pressKey(Key.A)
                keyUp(Key.CtrlLeft)
            }

        onNodeWithContentDescription(resolver.invoke(Strings.Copy))
            .assertExists()

        onRoot()
            .performKeyInput {
                pressKey(Key.Escape)
            }

        onNodeWithContentDescription(resolver.invoke(Strings.Copy))
            .assertDoesNotExist()
    }

    @Test
    fun glider_is_pasted_correctly_with_keyboard_shortcuts() = runUiTest(
        generalTestDispatcher,
    ) { uiGraph ->
        val uiEntryPoint = uiGraph.interactiveCellUniverseTestsUiEntryPoint

        lateinit var clipboardReaderWriter: ClipboardReaderWriter
        lateinit var resolver: (ParameterizedString) -> String

        setContent {
            resolver = parameterizedStringResolver()
            val temporalGameOfLifeState = rememberTemporalGameOfLifeState(
                targetStepsPerSecond = 60.0,
            )

            val temporalGameOfLifeStateMutator = rememberTemporalGameOfLifeStateMutator(
                temporalGameOfLifeState = temporalGameOfLifeState,
                gameOfLifeAlgorithm = gameOfLifeAlgorithm,
                clock = cellTickerTestDispatcher.scheduler.clock,
                dispatchers = dispatchers,
            )

            LaunchedEffect(temporalGameOfLifeStateMutator) {
                temporalGameOfLifeStateMutator.update()
            }

            with(uiEntryPoint.interactiveCellUniverseEntryPoint) {
                clipboardReaderWriter = rememberFakeClipboardReaderWriter()

                InteractiveCellUniverse(
                    temporalGameOfLifeState = temporalGameOfLifeState,
                    windowSizeClass = currentWindowAdaptiveInfo().windowSizeClass,
                    onSeeMoreSettingsClicked = {},
                    onOpenInSettingsClicked = {},
                    onViewDeserializationInfo = {},
                    modifier = Modifier.fillMaxSize(),
                    interactiveCellUniverseState = rememberInteractiveCellUniverseState(
                        temporalGameOfLifeState = temporalGameOfLifeState,
                        mutableCellWindowViewportState = rememberMutableCellWindowViewportState(
                            offset = Offset(30.5f, -18.5f),
                        ),
                        clipboardReaderWriter = clipboardReaderWriter,
                    ),
                )
            }
        }

        onRoot()
            .performKeyInput {
                pressKey(Key.Spacebar)
            }

        clipboardReaderWriter.setText(
            """
            #R 0 0
            x = 3, y = 3, rule = B3/S23
            bo$2bo$3o!
            """.trimIndent(),
        )

        onRoot()
            .performKeyInput {
                keyDown(Key.CtrlLeft)
                pressKey(Key.V)
                keyUp(Key.CtrlLeft)
            }

        generalTestDispatcher.scheduler.advanceUntilIdle()
        waitForIdle()

        onNodeWithContentDescription(resolver.invoke(Strings.ApplyPaste))
            .performClick()

        assertNodesAreAlive(
            resolver = resolver,
            cells = setOf(
                IntOffset(31, -19),
                IntOffset(32, -18),
                IntOffset(30, -17),
                IntOffset(31, -17),
                IntOffset(32, -17),
            ),
        )
    }
}

@OptIn(ExperimentalTestApi::class)
private fun ComposeUiTest.assertNodesAreAlive(resolver: (ParameterizedString) -> String, cells: Set<IntOffset>) {
    cells.forEach { cell ->
        if (
            onAllNodesWithContentDescription(
                resolver.invoke(CellsStrings.InteractableCellContentDescription(cell.x, cell.y)),
            ).fetchSemanticsNodes().isEmpty()
        ) {
            scrollToCell(cell)
        }

        onNodeWithContentDescription(
            resolver.invoke(CellsStrings.InteractableCellContentDescription(cell.x, cell.y)),
        )
            .assertIsOn()
    }
}

@OptIn(ExperimentalTestApi::class)
private fun ComposeUiTest.scrollToCell(cell: IntOffset) {
    onNodeWithTag("MutableCellWindow")
        .onChildren()
        .filterToOne(hasScrollToIndexAction())
        .performScrollToIndex(cell.toRingIndex())
}
