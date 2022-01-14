package com.alexvanyo.composelife.ui
import androidx.compose.foundation.layout.size
import androidx.compose.ui.Modifier
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.graphics.ImageBitmap
import androidx.compose.ui.graphics.PixelMap
import androidx.compose.ui.graphics.toPixelMap
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.test.captureToImage
import androidx.compose.ui.test.junit4.createComposeRule
import androidx.compose.ui.test.onRoot
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntRect
import androidx.compose.ui.unit.IntSize
import androidx.test.ext.junit.runners.AndroidJUnit4
import com.alexvanyo.composelife.model.GameOfLifeState
import com.alexvanyo.composelife.model.toCellState
import com.alexvanyo.composelife.ui.theme.ComposeLifeTheme
import org.junit.Assert.assertEquals
import org.junit.Rule
import org.junit.Test
import org.junit.runner.RunWith

@RunWith(AndroidJUnit4::class)
class NonInteractableCellTests {

    @get:Rule
    val composeTestRule = createComposeRule()

    @Test
    fun non_interactable_cells_draws_correctly_dark_mode() {
        val cellState = setOf(
            0 to 0,
            2 to 0,
            4 to 0,
            0 to 2,
            2 to 2,
            4 to 2,
            0 to 4,
            2 to 4,
            4 to 4
        ).toCellState()

        composeTestRule.setContent {
            ComposeLifeTheme(darkTheme = true) {
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
                            4 to 4
                        ).toCellState()
                    ),
                    scaledCellDpSize = with(LocalDensity.current) { 1.toDp() },
                    cellWindow = IntRect(
                        IntOffset(0, 0),
                        IntOffset(9, 9)
                    ),
                    modifier = Modifier.size(with(LocalDensity.current) { 10.toDp() })
                )
            }
        }

        composeTestRule.onRoot().captureToImage().assertPixels(
            IntSize(10, 10)
        ) {
            if (it in cellState.aliveCells) {
                Color.White
            } else {
                Color.Black
            }
        }
    }

    @Test
    fun non_interactable_cells_draws_correctly_light_mode() {
        val cellState = setOf(
            0 to 0,
            2 to 0,
            4 to 0,
            0 to 2,
            2 to 2,
            4 to 2,
            0 to 4,
            2 to 4,
            4 to 4
        ).toCellState()

        composeTestRule.setContent {
            ComposeLifeTheme(darkTheme = false) {
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
                            4 to 4
                        ).toCellState()
                    ),
                    scaledCellDpSize = with(LocalDensity.current) { 1.toDp() },
                    cellWindow = IntRect(
                        IntOffset(0, 0),
                        IntOffset(9, 9)
                    ),
                    modifier = Modifier.size(with(LocalDensity.current) { 10.toDp() })
                )
            }
        }

        composeTestRule.onRoot().captureToImage().assertPixels(
            IntSize(10, 10)
        ) {
            if (it in cellState.aliveCells) {
                Color.Black
            } else {
                Color.White
            }
        }
    }
}

private fun ImageBitmap.assertPixels(
    expectedSize: IntSize? = null,
    expectedColorProvider: (position: IntOffset) -> Color?
) {
    if (expectedSize != null) {
        assertEquals(
            expectedSize,
            IntSize(width, height)
        )
    }

    val pixelMap = toPixelMap()
    (0 until width).forEach { x ->
        (0 until height).forEach { y ->
            val expectedColor = expectedColorProvider(IntOffset(x, y))
            if (expectedColor != null) {
                pixelMap.assertPixelColor(expectedColor, x, y)
            }
        }
    }
}

private fun PixelMap.assertPixelColor(
    expected: Color,
    x: Int,
    y: Int
) {
    val color = this[x, y]
    val errorString = "Pixel($x, $y) was expected to be $expected, but was $color"
    assertEquals(errorString, expected.red, color.red, 0.02f)
    assertEquals(errorString, expected.green, color.green, 0.02f)
    assertEquals(errorString, expected.blue, color.blue, 0.02f)
    assertEquals(errorString, expected.alpha, color.alpha, 0.02f)
}
