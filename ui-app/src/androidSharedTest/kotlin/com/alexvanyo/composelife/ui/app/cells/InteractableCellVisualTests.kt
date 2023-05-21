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
import androidx.compose.foundation.background
import androidx.compose.foundation.layout.size
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.test.junit4.createComposeRule
import androidx.compose.ui.test.onRoot
import androidx.compose.ui.unit.IntSize
import androidx.test.ext.junit.runners.AndroidJUnit4
import com.alexvanyo.composelife.preferences.CurrentShape
import com.alexvanyo.composelife.screenshot.assertPixels
import com.alexvanyo.composelife.screenshot.captureToImage
import com.alexvanyo.composelife.ui.app.theme.ComposeLifeTheme
import org.junit.Assume.assumeTrue
import org.junit.Rule
import org.junit.runner.RunWith
import kotlin.test.Test

@RunWith(AndroidJUnit4::class)
class InteractableCellVisualTests {

    @get:Rule
    val composeTestRule = createComposeRule()

    @Test
    fun alive_interactable_cell_draws_correctly_dark_mode() {
        assumeTrue(Build.VERSION.SDK_INT >= 28)
        if (Build.VERSION.SDK_INT < 28) return

        var aliveCellColor: Color? = null

        composeTestRule.setContent {
            ComposeLifeTheme(darkTheme = true) {
                InteractableCell(
                    drawState = DrawState.Alive,
                    shape = CurrentShape.RoundRectangle(
                        sizeFraction = 1f,
                        cornerFraction = 0f,
                    ),
                    contentDescription = "",
                    onValueChange = {},
                    modifier = Modifier
                        .size(with(LocalDensity.current) { 10.toDp() })
                        .background(ComposeLifeTheme.deadCellColor),
                )

                aliveCellColor = ComposeLifeTheme.aliveCellColor
            }
        }

        composeTestRule.onRoot().captureToImage().assertPixels(
            IntSize(10, 10),
        ) {
            @Suppress("UnsafeCallOnNullableType")
            aliveCellColor!!
        }
    }

    @Test
    fun alive_interactable_cell_draws_correctly_light_mode() {
        assumeTrue(Build.VERSION.SDK_INT >= 28)
        if (Build.VERSION.SDK_INT < 28) return

        var aliveCellColor: Color? = null

        composeTestRule.setContent {
            ComposeLifeTheme(darkTheme = false) {
                InteractableCell(
                    drawState = DrawState.Alive,
                    shape = CurrentShape.RoundRectangle(
                        sizeFraction = 1f,
                        cornerFraction = 0f,
                    ),
                    contentDescription = "",
                    onValueChange = {},
                    modifier = Modifier
                        .size(with(LocalDensity.current) { 10.toDp() })
                        .background(ComposeLifeTheme.deadCellColor),
                )

                aliveCellColor = ComposeLifeTheme.aliveCellColor
            }
        }

        composeTestRule.onRoot().captureToImage().assertPixels(
            IntSize(10, 10),
        ) {
            @Suppress("UnsafeCallOnNullableType")
            aliveCellColor!!
        }
    }

    @Test
    fun dead_interactable_cell_draws_correctly_dark_mode() {
        assumeTrue(Build.VERSION.SDK_INT >= 28)
        if (Build.VERSION.SDK_INT < 28) return

        var deadCellColor: Color? = null

        composeTestRule.setContent {
            ComposeLifeTheme(darkTheme = true) {
                InteractableCell(
                    drawState = DrawState.Dead,
                    shape = CurrentShape.RoundRectangle(
                        sizeFraction = 1f,
                        cornerFraction = 0f,
                    ),
                    contentDescription = "",
                    onValueChange = {},
                    modifier = Modifier
                        .size(with(LocalDensity.current) { 10.toDp() })
                        .background(ComposeLifeTheme.deadCellColor),
                )

                deadCellColor = ComposeLifeTheme.deadCellColor
            }
        }

        composeTestRule.onRoot().captureToImage().assertPixels(
            IntSize(10, 10),
        ) {
            @Suppress("UnsafeCallOnNullableType")
            deadCellColor!!
        }
    }

    @Test
    fun dead_interactable_cell_draws_correctly_light_mode() {
        assumeTrue(Build.VERSION.SDK_INT >= 28)
        if (Build.VERSION.SDK_INT < 28) return

        var deadCellColor: Color? = null

        composeTestRule.setContent {
            ComposeLifeTheme(darkTheme = false) {
                InteractableCell(
                    drawState = DrawState.Dead,
                    shape = CurrentShape.RoundRectangle(
                        sizeFraction = 1f,
                        cornerFraction = 0f,
                    ),
                    contentDescription = "",
                    onValueChange = {},
                    modifier = Modifier
                        .size(with(LocalDensity.current) { 10.toDp() })
                        .background(ComposeLifeTheme.deadCellColor),
                )

                deadCellColor = ComposeLifeTheme.deadCellColor
            }
        }

        composeTestRule.onRoot().captureToImage().assertPixels(
            IntSize(10, 10),
        ) {
            @Suppress("UnsafeCallOnNullableType")
            deadCellColor!!
        }
    }
}
