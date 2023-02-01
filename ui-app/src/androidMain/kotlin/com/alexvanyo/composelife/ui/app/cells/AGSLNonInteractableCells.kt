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

import android.graphics.Bitmap
import android.graphics.BitmapShader
import android.graphics.Color
import android.graphics.RuntimeShader
import android.graphics.Shader
import androidx.annotation.RequiresApi
import androidx.compose.foundation.Canvas
import androidx.compose.runtime.Composable
import androidx.compose.runtime.DisposableEffect
import androidx.compose.runtime.remember
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.graphics.ShaderBrush
import androidx.compose.ui.graphics.toArgb
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.unit.Dp
import androidx.compose.ui.unit.IntRect
import androidx.core.graphics.set
import com.alexvanyo.composelife.model.GameOfLifeState
import com.alexvanyo.composelife.preferences.CurrentShape
import com.alexvanyo.composelife.ui.app.theme.ComposeLifeTheme
import org.intellij.lang.annotations.Language

@Language("AGSL")
private val SHADER_SRC = """
    // The cell shader, as a mask.
    uniform shader cells;
    
    // The color of an alive cell
    layout(color) uniform float4 aliveColor;
    
    // The background (dead) color
    layout(color) uniform float4 deadColor;
    
    // The size of the cell window
    uniform int2 cellWindowSize;
    
    // The pixel size of a single cell
    uniform float scaledCellPixelSize;
    
    // The pixel translation of the center cell from the center
    uniform float2 pixelOffsetFromCenter;

    // The type of shape to draw for an alive cell
    uniform int shapeType;
    
    // The size of the rectangle
    uniform float sizeFraction;
    
    // The size of the corner
    uniform float cornerFraction;
    
    // The size of the viewport
    uniform float2 size;
    
    float roundRectangleSDF(float2 centerPosition, float2 size, float radius) {
        return length(max(abs(centerPosition) - size + radius, 0.0)) - radius;
    }

    float4 roundRectangleCell(float2 offsetFromCenter) {
        float distance = roundRectangleSDF(
            offsetFromCenter - float2(0.5),
            float2(sizeFraction / 2.0),
            cornerFraction * sizeFraction
        );
        
        if (distance <= 0.0) {
            return aliveColor;
        } else {
            return deadColor;
        }
    }
    
    float4 main(float2 fragCoord) {
        float2 cellWindowPixelSize = scaledCellPixelSize * float2(cellWindowSize);
        float2 offsetFromCellWindow = (size - cellWindowPixelSize) / 2.0 - pixelOffsetFromCenter;
        float2 cellCoordinates = (fragCoord - offsetFromCellWindow) / scaledCellPixelSize;
        
        if (cells.eval(cellCoordinates).r != 0.0) {
            if (shapeType == 0) {
                return roundRectangleCell(fract(cellCoordinates));
            } else {
                return aliveColor;
            }
        } else {
            return deadColor;
        }
    }
""".trimMargin()

@RequiresApi(33)
@Suppress("LongParameterList", "LongMethod")
@Composable
fun AGSLNonInteractableCells(
    gameOfLifeState: GameOfLifeState,
    scaledCellDpSize: Dp,
    cellWindow: IntRect,
    shape: CurrentShape,
    pixelOffsetFromCenter: Offset,
    modifier: Modifier = Modifier,
) {
    val scaledCellPixelSize = with(LocalDensity.current) { scaledCellDpSize.toPx() }

    val aliveColor = ComposeLifeTheme.aliveCellColor
    val deadColor = ComposeLifeTheme.deadCellColor

    val shader = remember {
        RuntimeShader(SHADER_SRC)
    }

    val cellBitmap = remember(cellWindow) {
        Bitmap.createBitmap(cellWindow.width + 1, cellWindow.height + 1, Bitmap.Config.ARGB_8888)
    }
    val cellBitmapShader = remember(cellBitmap) {
        BitmapShader(cellBitmap, Shader.TileMode.CLAMP, Shader.TileMode.CLAMP)
    }

    DisposableEffect(shader, shape) {
        when (shape) {
            is CurrentShape.RoundRectangle -> {
                shader.setIntUniform("shapeType", 0)
                shader.setFloatUniform("sizeFraction", shape.sizeFraction)
                shader.setFloatUniform("cornerFraction", shape.cornerFraction)
            }
        }

        onDispose {}
    }

    DisposableEffect(shader, aliveColor, deadColor) {
        shader.setColorUniform("aliveColor", aliveColor.toArgb())
        shader.setColorUniform("deadColor", deadColor.toArgb())

        onDispose {}
    }

    DisposableEffect(shader, cellBitmapShader) {
        shader.setInputBuffer("cells", cellBitmapShader)

        onDispose {}
    }

    DisposableEffect(shader, cellWindow) {
        shader.setIntUniform("cellWindowSize", cellWindow.width + 1, cellWindow.height + 1)

        onDispose {}
    }

    DisposableEffect(shader, pixelOffsetFromCenter) {
        shader.setFloatUniform("pixelOffsetFromCenter", pixelOffsetFromCenter.x, pixelOffsetFromCenter.y)

        onDispose {}
    }

    DisposableEffect(shader, scaledCellPixelSize) {
        shader.setFloatUniform("scaledCellPixelSize", scaledCellPixelSize)

        onDispose {}
    }

    DisposableEffect(shader, cellBitmap, cellWindow, gameOfLifeState.cellState) {
        cellBitmap.eraseColor(Color.TRANSPARENT)
        gameOfLifeState.cellState.getAliveCellsInWindow(cellWindow).forEach { cell ->
            cellBitmap[cell.x - cellWindow.left, cell.y - cellWindow.top] = Color.WHITE
        }

        onDispose {}
    }

    val brush = remember(shader) { ShaderBrush(shader) }

    Canvas(
        modifier = modifier,
    ) {
        pixelOffsetFromCenter.let {}
        shader.setFloatUniform("size", size.width, size.height)

        drawRect(
            brush = brush,
        )
    }
}
