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

package com.alexvanyo.composelife.ui.app.cells

import androidx.compose.foundation.layout.Spacer
import androidx.compose.runtime.Composable
import androidx.compose.runtime.remember
import androidx.compose.ui.Modifier
import androidx.compose.ui.draw.drawWithCache
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.graphics.ImageBitmap
import androidx.compose.ui.graphics.ImageBitmapConfig
import androidx.compose.ui.graphics.ShaderBrush
import androidx.compose.ui.graphics.asSkiaBitmap
import androidx.compose.ui.graphics.toArgb
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.unit.Dp
import com.alexvanyo.composelife.model.CellWindow
import com.alexvanyo.composelife.model.GameOfLifeState
import com.alexvanyo.composelife.preferences.CurrentShape
import com.alexvanyo.composelife.ui.app.theme.ComposeLifeTheme
import org.intellij.lang.annotations.Language
import org.jetbrains.skia.IRect
import org.jetbrains.skia.RuntimeEffect
import org.jetbrains.skia.RuntimeShaderBuilder

@Language("SKSL")
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

@Suppress("LongParameterList")
@Composable
fun SKSLNonInteractableCells(
    gameOfLifeState: GameOfLifeState,
    scaledCellDpSize: Dp,
    cellWindow: CellWindow,
    shape: CurrentShape,
    pixelOffsetFromCenter: Offset,
    modifier: Modifier = Modifier,
) {
    val scaledCellPixelSize = with(LocalDensity.current) { scaledCellDpSize.toPx() }

    val aliveColor = ComposeLifeTheme.aliveCellColor
    val deadColor = ComposeLifeTheme.deadCellColor

    val runtimeEffect = remember { RuntimeEffect.makeForShader(SHADER_SRC) }
    val runtimeShaderBuilder = remember(runtimeEffect) { RuntimeShaderBuilder(runtimeEffect) }
    val cellBitmap = remember(cellWindow) {
        ImageBitmap(cellWindow.width, cellWindow.height, ImageBitmapConfig.Argb8888).asSkiaBitmap()
    }

    Spacer(
        modifier = modifier
            .drawWithCache {
                runtimeShaderBuilder.uniform("size", size.width, size.height)
                when (shape) {
                    is CurrentShape.RoundRectangle -> {
                        runtimeShaderBuilder.uniform("shapeType", 0)
                        runtimeShaderBuilder.uniform("sizeFraction", shape.sizeFraction)
                        runtimeShaderBuilder.uniform("cornerFraction", shape.cornerFraction)
                    }
                }
                runtimeShaderBuilder.uniform(
                    "aliveColor",
                    aliveColor.red,
                    aliveColor.green,
                    aliveColor.blue,
                    aliveColor.alpha,
                )
                runtimeShaderBuilder.uniform(
                    "deadColor",
                    deadColor.red,
                    deadColor.green,
                    deadColor.blue,
                    deadColor.alpha,
                )
                runtimeShaderBuilder.uniform("cellWindowSize", cellWindow.width, cellWindow.height)
                runtimeShaderBuilder.uniform("pixelOffsetFromCenter", pixelOffsetFromCenter.x, pixelOffsetFromCenter.y)
                runtimeShaderBuilder.uniform("scaledCellPixelSize", scaledCellPixelSize)

                cellBitmap.erase(Color.Transparent.toArgb())
                gameOfLifeState.cellState.getAliveCellsInWindow(cellWindow).forEach { cell ->
                    cellBitmap.erase(
                        Color.White.toArgb(),
                        IRect.makeXYWH(cell.x - cellWindow.left, cell.y - cellWindow.top, 1, 1),
                    )
                }

                runtimeShaderBuilder.child("cells", cellBitmap.makeShader())

                val brush = ShaderBrush(runtimeShaderBuilder.makeShader())

                onDrawWithContent {
                    drawRect(brush)
                }
            },
    )
}
