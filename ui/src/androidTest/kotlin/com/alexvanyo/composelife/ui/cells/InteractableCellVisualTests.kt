package com.alexvanyo.composelife.ui.cells

import android.os.Build
import androidx.compose.foundation.background
import androidx.compose.foundation.layout.size
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.test.captureToImage
import androidx.compose.ui.test.junit4.createComposeRule
import androidx.compose.ui.test.onRoot
import androidx.compose.ui.unit.IntSize
import androidx.test.ext.junit.runners.AndroidJUnit4
import com.alexvanyo.composelife.preferences.CurrentShape
import com.alexvanyo.composelife.screenshot.assertPixels
import com.alexvanyo.composelife.ui.theme.ComposeLifeTheme
import org.junit.Assume.assumeTrue
import org.junit.Rule
import org.junit.Test
import org.junit.runner.RunWith

@RunWith(AndroidJUnit4::class)
class InteractableCellVisualTests {

    @get:Rule
    val composeTestRule = createComposeRule()

    @Test
    fun alive_interactable_cell_draws_correctly_dark_mode() {
        assumeTrue(Build.VERSION.SDK_INT >= 26)

        var aliveCellColor: Color? = null

        composeTestRule.setContent {
            ComposeLifeTheme(darkTheme = true) {
                InteractableCell(
                    isAlive = true,
                    shape = CurrentShape.RoundRectangle(
                        sizeFraction = 1f,
                        cornerFraction = 0f
                    ),
                    contentDescription = "",
                    onValueChange = {},
                    modifier = Modifier
                        .size(with(LocalDensity.current) { 10.toDp() })
                        .background(ComposeLifeTheme.deadCellColor)
                )

                aliveCellColor = ComposeLifeTheme.aliveCellColor
            }
        }

        composeTestRule.onRoot().captureToImage().assertPixels(
            IntSize(10, 10)
        ) {
            aliveCellColor!!
        }
    }

    @Test
    fun alive_interactable_cell_draws_correctly_light_mode() {
        assumeTrue(Build.VERSION.SDK_INT >= 26)

        var aliveCellColor: Color? = null

        composeTestRule.setContent {
            ComposeLifeTheme(darkTheme = false) {
                InteractableCell(
                    isAlive = true,
                    shape = CurrentShape.RoundRectangle(
                        sizeFraction = 1f,
                        cornerFraction = 0f
                    ),
                    contentDescription = "",
                    onValueChange = {},
                    modifier = Modifier
                        .size(with(LocalDensity.current) { 10.toDp() })
                        .background(ComposeLifeTheme.deadCellColor)
                )

                aliveCellColor = ComposeLifeTheme.aliveCellColor
            }
        }

        composeTestRule.onRoot().captureToImage().assertPixels(
            IntSize(10, 10)
        ) {
            aliveCellColor
        }
    }

    @Test
    fun dead_interactable_cell_draws_correctly_dark_mode() {
        assumeTrue(Build.VERSION.SDK_INT >= 26)

        var deadCellColor: Color? = null

        composeTestRule.setContent {
            ComposeLifeTheme(darkTheme = true) {
                InteractableCell(
                    isAlive = false,
                    shape = CurrentShape.RoundRectangle(
                        sizeFraction = 1f,
                        cornerFraction = 0f
                    ),
                    contentDescription = "",
                    onValueChange = {},
                    modifier = Modifier
                        .size(with(LocalDensity.current) { 10.toDp() })
                        .background(ComposeLifeTheme.deadCellColor)
                )

                deadCellColor = ComposeLifeTheme.deadCellColor
            }
        }

        composeTestRule.onRoot().captureToImage().assertPixels(
            IntSize(10, 10)
        ) {
            deadCellColor
        }
    }

    @Test
    fun dead_interactable_cell_draws_correctly_light_mode() {
        assumeTrue(Build.VERSION.SDK_INT >= 26)

        var deadCellColor: Color? = null

        composeTestRule.setContent {
            ComposeLifeTheme(darkTheme = false) {
                InteractableCell(
                    isAlive = false,
                    shape = CurrentShape.RoundRectangle(
                        sizeFraction = 1f,
                        cornerFraction = 0f
                    ),
                    contentDescription = "",
                    onValueChange = {},
                    modifier = Modifier
                        .size(with(LocalDensity.current) { 10.toDp() })
                        .background(ComposeLifeTheme.deadCellColor)
                )

                deadCellColor = ComposeLifeTheme.deadCellColor
            }
        }

        composeTestRule.onRoot().captureToImage().assertPixels(
            IntSize(10, 10)
        ) {
            deadCellColor
        }
    }
}
