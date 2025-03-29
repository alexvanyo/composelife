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

package com.alexvanyo.composelife.ui.app.action

import android.os.SystemClock
import android.view.InputDevice
import android.view.MotionEvent
import androidx.compose.foundation.background
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.Spacer
import androidx.compose.foundation.layout.height
import androidx.compose.foundation.layout.size
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.platform.LocalViewConfiguration
import androidx.compose.ui.platform.ViewConfiguration
import androidx.compose.ui.platform.testTag
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.onNodeWithTag
import androidx.compose.ui.unit.center
import androidx.compose.ui.unit.dp
import androidx.compose.ui.unit.toOffset
import androidx.test.platform.app.InstrumentationRegistry
import com.alexvanyo.composelife.model.CellState
import com.alexvanyo.composelife.model.CellStateFormat
import com.alexvanyo.composelife.model.DeserializationResult
import com.alexvanyo.composelife.model.di.CellStateParserProvider
import com.alexvanyo.composelife.patterns.GliderPattern
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferences
import com.alexvanyo.composelife.test.BaseUiInjectTest
import com.alexvanyo.composelife.test.runUiTest
import com.alexvanyo.composelife.ui.app.TestComposeLifeApplicationComponent
import com.alexvanyo.composelife.ui.app.TestComposeLifeUiComponent
import com.alexvanyo.composelife.ui.app.createComponent
import com.alexvanyo.composelife.ui.app.kmpGetEntryPoint
import com.alexvanyo.composelife.ui.cells.CellWindowInjectEntryPoint
import com.alexvanyo.composelife.ui.cells.CellWindowLocalEntryPoint
import com.alexvanyo.composelife.ui.cells.cellStateDragAndDropTarget
import com.alexvanyo.composelife.ui.cells.rememberMutableCellStateDropStateHolder
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.test.runCurrent
import kotlin.test.Test
import kotlin.test.assertEquals

@OptIn(ExperimentalTestApi::class, ExperimentalCoroutinesApi::class)
class LoadedCellStatePreviewTests : BaseUiInjectTest<TestComposeLifeApplicationComponent, TestComposeLifeUiComponent>(
    TestComposeLifeApplicationComponent::createComponent,
    TestComposeLifeUiComponent::createComponent,
) {
    private val entryPoint get() = applicationComponent.kmpGetEntryPoint()

    private val cellWindowLocalEntryPoint = object : CellWindowLocalEntryPoint {
        override val preferences = LoadedComposeLifePreferences.Defaults
    }

    @Test
    fun drag_and_drop_works_correctly() = runUiTest(
        entryPoint.generalTestDispatcher,
    ) { uiComponent, composeUiTest ->
        val cellWindowInjectEntryPoint: CellWindowInjectEntryPoint = uiComponent.entryPoint
        val cellStateParserProvider: CellStateParserProvider = uiComponent.entryPoint

        var droppedCellState: CellState? = null

        lateinit var viewConfiguration: ViewConfiguration

        composeUiTest.setContent {
            viewConfiguration = LocalViewConfiguration.current

            Column {
                with(cellWindowLocalEntryPoint) {
                    with(cellWindowInjectEntryPoint) {
                        LoadedCellStatePreview(
                            deserializationResult = DeserializationResult.Successful(
                                cellState = GliderPattern.seedCellState,
                                format = CellStateFormat.FixedFormat.Plaintext,
                                warnings = emptyList(),
                            ),
                            isPinned = false,
                            onPaste = {},
                            onPinChanged = {},
                            onViewDeserializationInfo = {},
                            modifier = Modifier
                                .testTag("LoadedCellStatePreview")
                                .height(200.dp),
                        )
                    }
                }

                with(cellStateParserProvider) {
                    Spacer(
                        modifier = Modifier
                            .testTag("TestDropTarget")
                            .cellStateDragAndDropTarget(
                                rememberMutableCellStateDropStateHolder { _, cellState ->
                                    droppedCellState = cellState
                                },
                            )
                            .size(100.dp)
                            .background(Color.Blue),
                    )
                }
            }
        }

        val automation = InstrumentationRegistry.getInstrumentation().uiAutomation
        val downTime = SystemClock.uptimeMillis()

        val loadedCellStatePreviewCenter =
            composeUiTest.onNodeWithTag("LoadedCellStatePreview").fetchSemanticsNode().let { node ->
                node.positionOnScreen + node.size.center.toOffset()
            }
        val testDropTargetCenter =
            composeUiTest.onNodeWithTag("TestDropTarget").fetchSemanticsNode().let { node ->
                node.positionOnScreen + node.size.center.toOffset()
            }

        val down = MotionEvent.obtain(
            downTime,
            downTime,
            MotionEvent.ACTION_DOWN,
            loadedCellStatePreviewCenter.x,
            loadedCellStatePreviewCenter.y,
            0,
        ).apply {
            source = InputDevice.SOURCE_TOUCHSCREEN
        }
        automation.injectInputEvent(down, true)
        down.recycle()

        composeUiTest.mainClock.advanceTimeBy(viewConfiguration.longPressTimeoutMillis + 100)

        val move = MotionEvent.obtain(
            downTime,
            SystemClock.uptimeMillis(),
            MotionEvent.ACTION_MOVE,
            testDropTargetCenter.x,
            testDropTargetCenter.y,
            0,
        ).apply {
            source = InputDevice.SOURCE_TOUCHSCREEN
        }
        automation.injectInputEvent(move, true)
        move.recycle()

        composeUiTest.waitForIdle()

        val up = MotionEvent.obtain(
            downTime,
            SystemClock.uptimeMillis(),
            MotionEvent.ACTION_UP,
            testDropTargetCenter.x,
            testDropTargetCenter.y,
            0,
        ).apply {
            source = InputDevice.SOURCE_TOUCHSCREEN
        }
        automation.injectInputEvent(up, true)
        up.recycle()

        composeUiTest.waitForIdle()
        runCurrent()

        assertEquals(GliderPattern.seedCellState, droppedCellState)
    }
}
