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

package com.alexvanyo.composelife.ui.cells

import android.os.SystemClock
import android.view.InputDevice
import android.view.MotionEvent
import androidx.compose.foundation.background
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.size
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.platform.testTag
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.longClick
import androidx.compose.ui.test.onNodeWithTag
import androidx.compose.ui.test.performTouchInput
import androidx.compose.ui.unit.center
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.toOffset
import androidx.test.platform.app.InstrumentationRegistry
import com.alexvanyo.composelife.kmpandroidrunner.KmpAndroidJUnit4
import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.model.di.CellStateParserProvider
import com.alexvanyo.composelife.patterns.GliderPattern
import com.alexvanyo.composelife.test.BaseUiInjectTest
import com.alexvanyo.composelife.test.runUiTest
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.test.runCurrent
import org.junit.runner.RunWith
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertIs
import kotlin.test.assertNull

@OptIn(ExperimentalTestApi::class, ExperimentalCoroutinesApi::class)
@RunWith(KmpAndroidJUnit4::class)
class CellStateDragAndDropTests : BaseUiInjectTest<
    TestComposeLifeApplicationComponent,
    TestComposeLifeApplicationEntryPoint,
    TestComposeLifeUiComponent,
    >(
    TestComposeLifeApplicationComponent::createComponent,
    TestComposeLifeUiComponent::createComponent,
) {

    @Test
    fun drag_and_drop_works_correctly_when_dropped() = runUiTest(
        applicationComponent.entryPoint.generalTestDispatcher,
    ) {
        val cellStateParserProvider: CellStateParserProvider = uiComponent.entryPoint

        lateinit var mutableCellStateDropStateHolder: MutableCellStateDropStateHolder

        var droppedOffset: Offset? = null
        var droppedCellState: CellState? = null

        setContent {
            with(cellStateParserProvider) {
                mutableCellStateDropStateHolder = rememberMutableCellStateDropStateHolder { dropOffset, cellState ->
                    droppedOffset = dropOffset
                    droppedCellState = cellState
                }
            }

            Column {
                Spacer(
                    modifier = Modifier
                        .testTag("TestDropSource")
                        .cellStateDragAndDropSource {
                            GliderPattern.seedCellState
                        }
                        .size(100.dp)
                        .background(Color.Red),
                )
                Spacer(
                    modifier = Modifier
                        .testTag("TestDropTarget")
                        .cellStateDragAndDropTarget(mutableCellStateDropStateHolder)
                        .size(100.dp)
                        .background(Color.Blue),
                )
            }
        }

        mutableCellStateDropStateHolder.cellStateDropState.let { cellStateDropState ->
            assertIs<CellStateDropState.None>(cellStateDropState)
        }

        val automation = InstrumentationRegistry.getInstrumentation().uiAutomation
        val downTime = SystemClock.uptimeMillis()

        val testDropSourceCenterScreenCoordinates: Offset =
            onNodeWithTag("TestDropSource").fetchSemanticsNode().let { node ->
                node.positionOnScreen + node.size.center.toOffset()
            }
        val testDropTargetCenterScreenCoordinates: Offset
        val testDropTargetCenterLocalCoordinates: Offset
        onNodeWithTag("TestDropTarget").fetchSemanticsNode().let { node ->
            testDropTargetCenterLocalCoordinates = node.size.center.toOffset()
            testDropTargetCenterScreenCoordinates = node.positionOnScreen + testDropTargetCenterLocalCoordinates
        }

        onNodeWithTag("TestDropSource").performTouchInput {
            longClick()
            val down = MotionEvent.obtain(
                downTime,
                downTime,
                MotionEvent.ACTION_DOWN,
                testDropSourceCenterScreenCoordinates.x,
                testDropSourceCenterScreenCoordinates.y,
                0,
            ).apply {
                source = InputDevice.SOURCE_TOUCHSCREEN
            }
            automation.injectInputEvent(down, true)
            down.recycle()
        }

        waitForIdle()
        runCurrent()

        mutableCellStateDropStateHolder.cellStateDropState.let { cellStateDropState ->
            assertIs<CellStateDropState.ApplicableDropAvailable>(cellStateDropState)
        }

        val move = MotionEvent.obtain(
            downTime,
            SystemClock.uptimeMillis(),
            MotionEvent.ACTION_MOVE,
            testDropTargetCenterScreenCoordinates.x,
            testDropTargetCenterScreenCoordinates.y,
            0,
        ).apply {
            source = InputDevice.SOURCE_TOUCHSCREEN
        }
        automation.injectInputEvent(move, true)
        move.recycle()

        waitForIdle()
        runCurrent()

        mutableCellStateDropStateHolder.cellStateDropState.let { cellStateDropState ->
            assertIs<CellStateDropState.DropPreview>(cellStateDropState)
            assertEquals(GliderPattern.seedCellState, cellStateDropState.cellState)
            assertEquals(testDropTargetCenterLocalCoordinates, cellStateDropState.offset)
        }

        val up = MotionEvent.obtain(
            downTime,
            SystemClock.uptimeMillis(),
            MotionEvent.ACTION_UP,
            testDropTargetCenterScreenCoordinates.x,
            testDropTargetCenterScreenCoordinates.y,
            0,
        ).apply {
            source = InputDevice.SOURCE_TOUCHSCREEN
        }
        automation.injectInputEvent(up, true)
        up.recycle()

        waitForIdle()
        runCurrent()

        mutableCellStateDropStateHolder.cellStateDropState.let { cellStateDropState ->
            assertIs<CellStateDropState.None>(cellStateDropState)
        }
        assertEquals(GliderPattern.seedCellState, droppedCellState)
        assertEquals(testDropTargetCenterLocalCoordinates, droppedOffset)
    }

    @Test
    fun drag_and_drop_works_correctly_when_ended() = runUiTest(
        applicationComponent.entryPoint.generalTestDispatcher,
    ) {
        val cellStateParserProvider: CellStateParserProvider = uiComponent.entryPoint

        lateinit var mutableCellStateDropStateHolder: MutableCellStateDropStateHolder

        var droppedOffset: Offset? = null
        var droppedCellState: CellState? = null

        setContent {
            with(cellStateParserProvider) {
                mutableCellStateDropStateHolder = rememberMutableCellStateDropStateHolder { dropOffset, cellState ->
                    droppedOffset = dropOffset
                    droppedCellState = cellState
                }
            }

            Column {
                Spacer(
                    modifier = Modifier
                        .testTag("TestDropSource")
                        .cellStateDragAndDropSource {
                            GliderPattern.seedCellState
                        }
                        .size(100.dp)
                        .background(Color.Red),
                )
                Spacer(
                    modifier = Modifier
                        .testTag("TestDropTarget")
                        .cellStateDragAndDropTarget(mutableCellStateDropStateHolder)
                        .size(100.dp)
                        .background(Color.Blue),
                )
            }
        }

        mutableCellStateDropStateHolder.cellStateDropState.let { cellStateDropState ->
            assertIs<CellStateDropState.None>(cellStateDropState)
        }

        val automation = InstrumentationRegistry.getInstrumentation().uiAutomation
        val downTime = SystemClock.uptimeMillis()

        val testDropSourceCenterScreenCoordinates: Offset =
            onNodeWithTag("TestDropSource").fetchSemanticsNode().let { node ->
                node.positionOnScreen + node.size.center.toOffset()
            }
        val testDropTargetCenterScreenCoordinates: Offset
        val testDropTargetCenterLocalCoordinates: Offset
        onNodeWithTag("TestDropTarget").fetchSemanticsNode().let { node ->
            testDropTargetCenterLocalCoordinates = node.size.center.toOffset()
            testDropTargetCenterScreenCoordinates = node.positionOnScreen + testDropTargetCenterLocalCoordinates
        }

        onNodeWithTag("TestDropSource").performTouchInput {
            longClick()
            val down = MotionEvent.obtain(
                downTime,
                downTime,
                MotionEvent.ACTION_DOWN,
                testDropSourceCenterScreenCoordinates.x,
                testDropSourceCenterScreenCoordinates.y,
                0,
            ).apply {
                source = InputDevice.SOURCE_TOUCHSCREEN
            }
            automation.injectInputEvent(down, true)
            down.recycle()
        }

        waitForIdle()
        runCurrent()

        mutableCellStateDropStateHolder.cellStateDropState.let { cellStateDropState ->
            assertIs<CellStateDropState.ApplicableDropAvailable>(cellStateDropState)
        }

        val move1 = MotionEvent.obtain(
            downTime,
            SystemClock.uptimeMillis(),
            MotionEvent.ACTION_MOVE,
            testDropTargetCenterScreenCoordinates.x,
            testDropTargetCenterScreenCoordinates.y,
            0,
        ).apply {
            source = InputDevice.SOURCE_TOUCHSCREEN
        }
        automation.injectInputEvent(move1, true)
        move1.recycle()

        waitForIdle()
        runCurrent()

        mutableCellStateDropStateHolder.cellStateDropState.let { cellStateDropState ->
            assertIs<CellStateDropState.DropPreview>(cellStateDropState)
            assertEquals(GliderPattern.seedCellState, cellStateDropState.cellState)
            assertEquals(testDropTargetCenterLocalCoordinates, cellStateDropState.offset)
        }

        val move2 = MotionEvent.obtain(
            downTime,
            SystemClock.uptimeMillis(),
            MotionEvent.ACTION_MOVE,
            testDropSourceCenterScreenCoordinates.x,
            testDropSourceCenterScreenCoordinates.y,
            0,
        ).apply {
            source = InputDevice.SOURCE_TOUCHSCREEN
        }
        automation.injectInputEvent(move2, true)
        move2.recycle()

        waitForIdle()
        runCurrent()

        mutableCellStateDropStateHolder.cellStateDropState.let { cellStateDropState ->
            assertIs<CellStateDropState.ApplicableDropAvailable>(cellStateDropState)
        }

        val up = MotionEvent.obtain(
            downTime,
            SystemClock.uptimeMillis(),
            MotionEvent.ACTION_UP,
            testDropSourceCenterScreenCoordinates.x,
            testDropSourceCenterScreenCoordinates.y,
            0,
        ).apply {
            source = InputDevice.SOURCE_TOUCHSCREEN
        }
        automation.injectInputEvent(up, true)
        up.recycle()

        // Give time for the drag event to end
        SystemClock.sleep(500)

        waitForIdle()
        runCurrent()

        mutableCellStateDropStateHolder.cellStateDropState.let { cellStateDropState ->
            assertIs<CellStateDropState.None>(cellStateDropState)
        }
        assertNull(droppedCellState)
        assertNull(droppedOffset)
    }
}
