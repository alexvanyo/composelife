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

package com.alexvanyo.composelife.ui.cells

import android.os.Build
import androidx.compose.foundation.layout.size
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.onRoot
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import androidx.compose.ui.unit.IntSize
import com.alexvanyo.composelife.kmpandroidrunner.KmpAndroidJUnit4
import com.alexvanyo.composelife.model.CellWindow
import com.alexvanyo.composelife.model.GameOfLifeState
import com.alexvanyo.composelife.model.toCellState
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferences
import com.alexvanyo.composelife.screenshot.assertPixels
import com.alexvanyo.composelife.screenshot.captureToImage
import com.alexvanyo.composelife.test.BaseUiInjectTest
import com.alexvanyo.composelife.test.runUiTest
import com.alexvanyo.composelife.ui.mobile.ComposeLifeTheme
import org.junit.Assume.assumeTrue
import org.junit.runner.RunWith
import kotlin.test.Test

@OptIn(ExperimentalTestApi::class)
class NonInteractableCellsVisualTests :
    BaseUiInjectTest<TestComposeLifeApplicationComponent, TestComposeLifeUiComponent>(
        TestComposeLifeApplicationComponent::createComponent,
        TestComposeLifeUiComponent::createComponent,
    ) {
    private val nonInteractableCellsLocalEntryPoint = object : NonInteractableCellsLocalEntryPoint {
        override val preferences = LoadedComposeLifePreferences.Defaults.copy(
            disableAGSL = true,
            disableOpenGL = true,
        )
    }

    @Test
    fun non_interactable_cells_draws_correctly_dark_mode() = runUiTest {
        assumeTrue(Build.VERSION.SDK_INT >= 28)
        if (Build.VERSION.SDK_INT < 28) return@runUiTest

        val nonInteractableCellsInjectEntryPoint: NonInteractableCellsInjectEntryPoint = uiComponent.entryPoint

        val cellState = setOf(
            0 to 0,
            2 to 0,
            4 to 0,
            0 to 2,
            2 to 2,
            4 to 2,
            0 to 4,
            2 to 4,
            4 to 4,
        ).toCellState()

        var aliveCellColor: Color? = null
        var deadCellColor: Color? = null

        setContent {
            ComposeLifeTheme(darkTheme = true) {
                with(nonInteractableCellsInjectEntryPoint) {
                    with(nonInteractableCellsLocalEntryPoint) {
                        NonInteractableCells(
                            gameOfLifeState = GameOfLifeState(
                                setOf(
                                    0 to 0,
                                    2 to 0,
                                    4 to 0,
                                    0 to 2,
                                    2 to 2,
                                    4 to 2,
                                    0 to 4,
                                    2 to 4,
                                    4 to 4,
                                ).toCellState(),
                            ),
                            scaledCellDpSize = with(LocalDensity.current) { 1.toDp() },
                            cellWindow = CellWindow(
                                IntRect(
                                    IntOffset(0, 0),
                                    IntSize(10, 10),
                                ),
                            ),
                            pixelOffsetFromCenter = Offset.Zero,
                            isThumbnail = false,
                            modifier = Modifier.size(with(LocalDensity.current) { 10.toDp() }),
                        )
                    }
                }

                aliveCellColor = ComposeLifeTheme.aliveCellColor
                deadCellColor = ComposeLifeTheme.deadCellColor
            }
        }

        onRoot().captureToImage().assertPixels(
            IntSize(10, 10),
        ) {
            if (it in cellState.aliveCells) {
                @Suppress("UnsafeCallOnNullableType")
                aliveCellColor!!
            } else {
                @Suppress("UnsafeCallOnNullableType")
                deadCellColor!!
            }
        }
    }

    @Test
    fun non_interactable_cells_draws_correctly_light_mode() = runUiTest {
        assumeTrue(Build.VERSION.SDK_INT >= 28)
        if (Build.VERSION.SDK_INT < 28) return@runUiTest

        val nonInteractableCellsInjectEntryPoint: NonInteractableCellsInjectEntryPoint = uiComponent.entryPoint

        val cellState = setOf(
            0 to 0,
            2 to 0,
            4 to 0,
            0 to 2,
            2 to 2,
            4 to 2,
            0 to 4,
            2 to 4,
            4 to 4,
        ).toCellState()

        var aliveCellColor: Color? = null
        var deadCellColor: Color? = null

        setContent {
            ComposeLifeTheme(darkTheme = false) {
                with(nonInteractableCellsInjectEntryPoint) {
                    with(nonInteractableCellsLocalEntryPoint) {
                        NonInteractableCells(
                            gameOfLifeState = GameOfLifeState(
                                setOf(
                                    0 to 0,
                                    2 to 0,
                                    4 to 0,
                                    0 to 2,
                                    2 to 2,
                                    4 to 2,
                                    0 to 4,
                                    2 to 4,
                                    4 to 4,
                                ).toCellState(),
                            ),
                            scaledCellDpSize = with(LocalDensity.current) { 1.toDp() },
                            cellWindow = CellWindow(
                                IntRect(
                                    IntOffset(0, 0),
                                    IntSize(10, 10),
                                ),
                            ),
                            pixelOffsetFromCenter = Offset.Zero,
                            isThumbnail = false,
                            modifier = Modifier.size(with(LocalDensity.current) { 10.toDp() }),
                        )
                    }
                }

                aliveCellColor = ComposeLifeTheme.aliveCellColor
                deadCellColor = ComposeLifeTheme.deadCellColor
            }
        }

        onRoot().captureToImage().assertPixels(
            IntSize(10, 10),
        ) {
            if (it in cellState.aliveCells) {
                @Suppress("UnsafeCallOnNullableType")
                aliveCellColor!!
            } else {
                @Suppress("UnsafeCallOnNullableType")
                deadCellColor!!
            }
        }
    }
}
