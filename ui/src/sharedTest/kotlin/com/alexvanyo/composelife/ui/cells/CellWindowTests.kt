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

import android.content.Context
import androidx.activity.ComponentActivity
import androidx.compose.foundation.layout.size
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.test.assertIsOff
import androidx.compose.ui.test.assertIsOn
import androidx.compose.ui.test.junit4.createAndroidComposeRule
import androidx.compose.ui.test.onNodeWithContentDescription
import androidx.compose.ui.test.onRoot
import androidx.compose.ui.test.performTouchInput
import androidx.compose.ui.test.swipe
import androidx.compose.ui.unit.Density
import androidx.compose.ui.unit.dp
import androidx.test.ext.junit.runners.AndroidJUnit4
import com.alexvanyo.composelife.model.MutableGameOfLifeState
import com.alexvanyo.composelife.model.toCellState
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferences
import com.alexvanyo.composelife.ui.R
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.test.runTest
import org.junit.Rule
import org.junit.Test
import org.junit.runner.RunWith
import kotlin.test.assertTrue

@RunWith(AndroidJUnit4::class)
class CellWindowTests {

    @get:Rule
    val composeTestRule = createAndroidComposeRule<ComponentActivity>()

    private val context: Context get() = composeTestRule.activity

    private val cellWindowLocalEntryPoint = object : CellWindowLocalEntryPoint {
        override val preferences = LoadedComposeLifePreferences.Defaults
    }

    @Test
    fun cells_are_displayed_correctly() {
        val mutableGameOfLifeState = MutableGameOfLifeState(
            cellState = setOf(
                0 to 0,
                0 to 2,
                0 to 4,
                2 to 0,
                2 to 2,
                2 to 4,
                4 to 0,
                4 to 2,
                4 to 4,
            ).toCellState(),
        )

        composeTestRule.setContent {
            with(cellWindowLocalEntryPoint) {
                MutableCellWindow(
                    gameOfLifeState = mutableGameOfLifeState,
                    modifier = Modifier.size(50.dp),
                    cellWindowState = rememberCellWindowState(
                        offset = Offset(-0.5f, -0.5f),
                    ),
                    cellDpSize = 10.dp,
                )
            }
        }

        composeTestRule
            .onNodeWithContentDescription(
                context.getString(R.string.cell_content_description, 0, 0),
            )
            .assertIsOn()

        composeTestRule
            .onNodeWithContentDescription(
                context.getString(R.string.cell_content_description, 0, 1),
            )
            .assertIsOff()

        composeTestRule
            .onNodeWithContentDescription(
                context.getString(R.string.cell_content_description, 0, 2),
            )
            .assertIsOn()

        composeTestRule
            .onNodeWithContentDescription(
                context.getString(R.string.cell_content_description, 0, 4),
            )
            .assertDoesNotExist()

        composeTestRule
            .onNodeWithContentDescription(
                context.getString(R.string.cell_content_description, 2, 0),
            )
            .assertIsOn()

        composeTestRule
            .onNodeWithContentDescription(
                context.getString(R.string.cell_content_description, 2, 1),
            )
            .assertIsOff()

        composeTestRule
            .onNodeWithContentDescription(
                context.getString(R.string.cell_content_description, 2, 2),
            )
            .assertIsOn()
    }

    @Test
    @OptIn(ExperimentalCoroutinesApi::class)
    fun cells_are_displayed_correctly_after_scrolling() = runTest {
        val mutableGameOfLifeState = MutableGameOfLifeState(
            cellState = setOf(
                0 to 0,
                0 to 2,
                0 to 4,
                2 to 0,
                2 to 2,
                2 to 4,
                4 to 0,
                4 to 2,
                4 to 4,
            ).toCellState(),
        )

        val cellWindowState = CellWindowState()

        lateinit var density: Density

        composeTestRule.setContent {
            density = LocalDensity.current

            with(cellWindowLocalEntryPoint) {
                MutableCellWindow(
                    gameOfLifeState = mutableGameOfLifeState,
                    modifier = Modifier.size(150.dp),
                    cellWindowState = cellWindowState,
                    cellDpSize = 30.dp,
                )
            }
        }

        composeTestRule.onRoot().performTouchInput {
            with(density) {
                swipe(
                    Offset(135.dp.toPx(), 135.dp.toPx()),
                    Offset(15.dp.toPx(), 15.dp.toPx()),
                )
            }
        }

        composeTestRule.mainClock.advanceTimeBy(1000)
        composeTestRule.waitForIdle()

        assertTrue(cellWindowState.offset.x > 3f)
        assertTrue(cellWindowState.offset.y > 3f)
    }
}
