package com.alexvanyo.composelife.testutil

import androidx.compose.ui.graphics.Color
import androidx.compose.ui.graphics.ImageBitmap
import androidx.compose.ui.graphics.PixelMap
import androidx.compose.ui.graphics.toPixelMap
import androidx.compose.ui.unit.IntOffset
import androidx.compose.ui.unit.IntSize
import org.junit.Assert.assertEquals

fun ImageBitmap.assertPixels(
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
