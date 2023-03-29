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

package com.alexvanyo.composelife.ui.app.cells

import android.os.Build
import androidx.compose.foundation.layout.size
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.test.junit4.createComposeRule
import androidx.compose.ui.test.onRoot
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import androidx.compose.ui.unit.IntSize
import androidx.test.ext.junit.runners.AndroidJUnit4
import com.alexvanyo.composelife.model.GameOfLifeState
import com.alexvanyo.composelife.model.toCellState
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferences
import com.alexvanyo.composelife.screenshot.assertPixels
import com.alexvanyo.composelife.screenshot.captureToImage
import com.alexvanyo.composelife.ui.app.theme.ComposeLifeTheme
import org.junit.Assume.assumeTrue
import org.junit.Rule
import org.junit.runner.RunWith
import kotlin.test.Test

@RunWith(AndroidJUnit4::class)
class NonInteractableCellsVisualTests {

    @get:Rule
    val composeTestRule = createComposeRule()

    private val nonInteractableCellsLocalEntryPoint = object : NonInteractableCellsLocalEntryPoint {
        override val preferences = LoadedComposeLifePreferences.Defaults.copy(
            disableAGSL = true,
            disableOpenGL = true,
        )
    }

    @Test
    fun non_interactable_cells_draws_correctly_dark_mode() {
        assumeTrue(Build.VERSION.SDK_INT >= 26)

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

        composeTestRule.setContent {
            ComposeLifeTheme(darkTheme = true) {
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
                        cellWindow = IntRect(
                            IntOffset(0, 0),
                            IntOffset(9, 9),
                        ),
                        pixelOffsetFromCenter = Offset.Zero,
                        modifier = Modifier.size(with(LocalDensity.current) { 10.toDp() }),
                    )
                }

                aliveCellColor = ComposeLifeTheme.aliveCellColor
                deadCellColor = ComposeLifeTheme.deadCellColor
            }
        }

        composeTestRule.onRoot().captureToImage().assertPixels(
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
    fun non_interactable_cells_draws_correctly_light_mode() {
        assumeTrue(Build.VERSION.SDK_INT >= 26)

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

        composeTestRule.setContent {
            ComposeLifeTheme(darkTheme = false) {
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
                        cellWindow = IntRect(
                            IntOffset(0, 0),
                            IntOffset(9, 9),
                        ),
                        pixelOffsetFromCenter = Offset.Zero,
                        modifier = Modifier.size(with(LocalDensity.current) { 10.toDp() }),
                    )
                }

                aliveCellColor = ComposeLifeTheme.aliveCellColor
                deadCellColor = ComposeLifeTheme.deadCellColor
            }
        }

        composeTestRule.onRoot().captureToImage().assertPixels(
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
