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

import android.app.ActivityManager
import android.opengl.GLES20
import android.opengl.GLSurfaceView
import android.opengl.Matrix
import androidx.compose.runtime.Composable
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.graphics.Color
import androidx.compose.ui.platform.LocalContext
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.unit.Dp
import androidx.compose.ui.unit.IntRect
import androidx.compose.ui.unit.IntSize
import androidx.compose.ui.viewinterop.AndroidView
import androidx.core.content.getSystemService
import com.alexvanyo.composelife.model.GameOfLifeState
import com.alexvanyo.composelife.preferences.CurrentShape
import com.alexvanyo.composelife.ui.theme.ComposeLifeTheme
import kotlinx.coroutines.asCoroutineDispatcher
import kotlinx.coroutines.flow.MutableStateFlow
import kotlinx.coroutines.flow.collect
import kotlinx.coroutines.flow.flowOn
import kotlinx.coroutines.flow.onEach
import kotlinx.coroutines.launch
import org.intellij.lang.annotations.Language
import java.nio.ByteBuffer
import java.nio.ByteOrder
import java.nio.FloatBuffer
import java.nio.ShortBuffer
import java.util.concurrent.Executor
import javax.microedition.khronos.egl.EGLConfig
import javax.microedition.khronos.opengles.GL10

@Composable
fun openGLSupported(): Boolean {
    val context = LocalContext.current
    val activityManager = remember(context) {
        context.getSystemService<ActivityManager>()
    }
    return (activityManager?.deviceConfigurationInfo?.reqGlEsVersion ?: 0) >= 0x00020000
}

@Suppress("LongParameterList")
@Composable
fun OpenGLNonInteractableCells(
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

    val cellsBuffer = remember(cellWindow, gameOfLifeState.cellState) {
        val buffer = ByteBuffer.allocate((cellWindow.width + 1) * (cellWindow.height + 1))

        gameOfLifeState.cellState.getAliveCellsInWindow(cellWindow).forEach { cell ->
            buffer.put((cell.y - cellWindow.top) * (cellWindow.width + 1) + cell.x - cellWindow.left, 0xf)
        }

        buffer
    }

    val screenShapeParameters = when (shape) {
        is CurrentShape.RoundRectangle -> {
            ScreenShapeParameters.RoundRectangle(
                cells = cellsBuffer,
                aliveColor = aliveColor,
                deadColor = deadColor,
                cellWindowSize = IntSize(cellWindow.width + 1, cellWindow.height + 1),
                scaledCellPixelSize = scaledCellPixelSize,
                pixelOffsetFromCenter = pixelOffsetFromCenter,
                sizeFraction = shape.sizeFraction,
                cornerFraction = shape.cornerFraction,
            )
        }
    }

    val coroutineScope = rememberCoroutineScope()

    AndroidView(
        factory = { context ->
            object : GLSurfaceView(context) {
                val parameters = MutableStateFlow(screenShapeParameters)

                val renderer = object : Renderer {
                    private val projectionMatrix = FloatArray(16)
                    private val mvpMatrix = FloatArray(16)
                    private val viewMatrix = FloatArray(16)

                    lateinit var screenShape: ScreenShape

                    override fun onSurfaceCreated(unused: GL10?, config: EGLConfig?) {
                        GLES20.glClearColor(0f, 0f, 0f, 0f)
                        screenShape = ScreenShape()
                        screenShape.setScreenShapeParameters(parameters.value)
                    }

                    override fun onSurfaceChanged(unused: GL10?, width: Int, height: Int) {
                        GLES20.glViewport(0, 0, width, height)

                        Matrix.orthoM(projectionMatrix, 0, 0f, 1f, 0f, 1f, 0.5f, 2f)
                        Matrix.setLookAtM(viewMatrix, 0, 0f, 0f, 1f, 0f, 0f, 0f, 0f, 1f, 0f)
                        Matrix.multiplyMM(mvpMatrix, 0, projectionMatrix, 0, viewMatrix, 0)

                        screenShape.setSize(width, height)
                    }

                    override fun onDrawFrame(unused: GL10?) {
                        screenShape.draw(mvpMatrix)
                    }

                    fun setParameters(screenShapeParameters: ScreenShapeParameters) {
                        if (::screenShape.isInitialized) {
                            screenShape.setScreenShapeParameters(screenShapeParameters)
                        }
                    }
                }
            }.apply {
                setEGLContextClientVersion(2)
                setRenderer(renderer)

                val openGLExecutor = Executor(::queueEvent)
                val openGLDispatcher = openGLExecutor.asCoroutineDispatcher()

                coroutineScope.launch {
                    parameters
                        .onEach(renderer::setParameters)
                        .flowOn(openGLDispatcher)
                        .collect()
                }
            }
        },
        update = {
            it.parameters.value = screenShapeParameters
        },
        modifier = modifier,
    )
}

sealed interface ScreenShapeParameters {
    val cells: ByteBuffer
    val aliveColor: Color
    val deadColor: Color
    val cellWindowSize: IntSize
    val scaledCellPixelSize: Float
    val pixelOffsetFromCenter: Offset

    data class RoundRectangle(
        override val cells: ByteBuffer,
        override val aliveColor: Color,
        override val deadColor: Color,
        override val cellWindowSize: IntSize,
        override val scaledCellPixelSize: Float,
        override val pixelOffsetFromCenter: Offset,
        val sizeFraction: Float,
        val cornerFraction: Float,
    ) : ScreenShapeParameters
}

@Language("GLSL")
private val vertexShaderCode = """
    uniform mat4 mvpMatrix;
    attribute vec4 position;
    void main() {
        gl_Position = mvpMatrix * position;
    }
""".trimIndent()

@Language("GLSL")
private val fragmentShaderCode = """
    precision mediump float;
    
    // The cell shader, as a mask.
    uniform sampler2D cells;
    
    // The color of an alive cell
    uniform vec4 aliveColor;
    
    // The background (dead) color
    uniform vec4 deadColor;
    
    // The size of the cell window
    uniform ivec2 cellWindowSize;
    
    // The pixel size of a single cell
    uniform float scaledCellPixelSize;
    
    // The pixel translation of the center cell from the center
    uniform vec2 pixelOffsetFromCenter;
    
    // The type of shape to draw for an alive cell
    uniform int shapeType;
    
    // The size of the round rectangle
    uniform float sizeFraction;
    
    // The size of the round rectangle corner
    uniform float cornerFraction;
    
    // The size of the viewport
    uniform ivec2 size;
    
    float roundRectangleSDF(vec2 centerPosition, vec2 size, float radius) {
        return length(max(abs(centerPosition) - size + radius, 0.0)) - radius;
    }

    vec4 roundRectangleCell(vec2 offsetFromCenter) {
        float distance = roundRectangleSDF(
            offsetFromCenter - vec2(0.5),
            vec2(sizeFraction / 2.0),
            cornerFraction * sizeFraction
        );
        
        if (distance <= 0.0) {
            return aliveColor;
        } else {
            return deadColor;
        }
    }
    
    void main() {
        vec2 cellWindowPixelSize = scaledCellPixelSize * vec2(cellWindowSize);
        vec2 offsetFromCellWindow = (vec2(size) - cellWindowPixelSize) / 2.0 - pixelOffsetFromCenter * vec2(1, -1);
        vec2 cellCoordinates = (gl_FragCoord.xy - offsetFromCellWindow) / scaledCellPixelSize;
        vec2 normalizedCellCoordinates = vec2(
            cellCoordinates.x / float(cellWindowSize.x),
            1.0 - cellCoordinates.y / float(cellWindowSize.y)
        );
        
        if (texture2D(cells, normalizedCellCoordinates).a != 0.0) {
            if (shapeType == 0) {
                gl_FragColor = roundRectangleCell(fract(cellCoordinates));
            }
        } else {
            gl_FragColor = deadColor;
        }
    }
""".trimIndent()

class ScreenShape {

    private val coords = floatArrayOf(
        0f, 1f, 0f,
        0f, 0f, 0f,
        1f, 0f, 0f,
        1f, 1f, 0f,
    )

    private val drawOrder = shortArrayOf(0, 1, 2, 0, 2, 3)

    private val coordsPerVertex = 3

    private val vertexStride = coordsPerVertex * 4

    private val vertexBuffer: FloatBuffer =
        ByteBuffer.allocateDirect(coords.size * 4).run {
            order(ByteOrder.nativeOrder())
            asFloatBuffer().apply {
                put(coords)
                position(0)
            }
        }

    private val drawListBuffer: ShortBuffer =
        ByteBuffer.allocateDirect(drawOrder.size * 2).run {
            order(ByteOrder.nativeOrder())
            asShortBuffer().apply {
                put(drawOrder)
                position(0)
            }
        }

    private val vertexShader = loadShader(
        GLES20.GL_VERTEX_SHADER,
        vertexShaderCode,
    )

    private val fragmentShader = loadShader(
        GLES20.GL_FRAGMENT_SHADER,
        fragmentShaderCode,
    )

    private val program = GLES20.glCreateProgram().apply {
        GLES20.glAttachShader(this, vertexShader)
        GLES20.glAttachShader(this, fragmentShader)
        GLES20.glLinkProgram(this)
    }

    private val positionHandle = GLES20.glGetAttribLocation(program, "position")
    private val cellsHandle = GLES20.glGetUniformLocation(program, "cells")
    private val aliveColorHandle = GLES20.glGetUniformLocation(program, "aliveColor")
    private val deadColorHandle = GLES20.glGetUniformLocation(program, "deadColor")
    private val cellWindowSizeHandle = GLES20.glGetUniformLocation(program, "cellWindowSize")
    private val scaledCellPixelSizeHandle = GLES20.glGetUniformLocation(program, "scaledCellPixelSize")
    private val pixelOffsetFromCenterHandle = GLES20.glGetUniformLocation(program, "pixelOffsetFromCenter")
    private val shapeTypeHandle = GLES20.glGetUniformLocation(program, "shapeType")
    private val sizeFractionHandle = GLES20.glGetUniformLocation(program, "sizeFraction")
    private val cornerFractionHandle = GLES20.glGetUniformLocation(program, "cornerFraction")
    private val sizeHandle = GLES20.glGetUniformLocation(program, "size")
    private val mvpMatrixHandle = GLES20.glGetUniformLocation(program, "mvpMatrix")

    private val textureHandle = run {
        val array = IntArray(1)
        GLES20.glGenTextures(0, array, 0)
        array[0]
    }

    fun setSize(width: Int, height: Int) {
        GLES20.glUseProgram(program)
        GLES20.glUniform2i(sizeHandle, width, height)
    }

    fun setScreenShapeParameters(screenShapeParameters: ScreenShapeParameters) {
        GLES20.glUseProgram(program)
        GLES20.glTexParameteri(GLES20.GL_TEXTURE_2D, GLES20.GL_TEXTURE_WRAP_S, GLES20.GL_REPEAT)
        GLES20.glTexParameteri(GLES20.GL_TEXTURE_2D, GLES20.GL_TEXTURE_WRAP_T, GLES20.GL_REPEAT)
        GLES20.glTexParameteri(GLES20.GL_TEXTURE_2D, GLES20.GL_TEXTURE_MIN_FILTER, GLES20.GL_NEAREST)
        GLES20.glTexParameteri(GLES20.GL_TEXTURE_2D, GLES20.GL_TEXTURE_MAG_FILTER, GLES20.GL_NEAREST)
        GLES20.glActiveTexture(GLES20.GL_TEXTURE0)
        GLES20.glBindTexture(GLES20.GL_TEXTURE_2D, textureHandle)
        GLES20.glPixelStorei(GLES20.GL_UNPACK_ALIGNMENT, 1)
        GLES20.glTexImage2D(
            GLES20.GL_TEXTURE_2D,
            0,
            GLES20.GL_ALPHA,
            screenShapeParameters.cellWindowSize.width,
            screenShapeParameters.cellWindowSize.height,
            0,
            GLES20.GL_ALPHA,
            GLES20.GL_UNSIGNED_BYTE,
            screenShapeParameters.cells,
        )
        GLES20.glUniform1i(cellsHandle, 0)
        GLES20.glUniform4f(
            aliveColorHandle,
            screenShapeParameters.aliveColor.red,
            screenShapeParameters.aliveColor.green,
            screenShapeParameters.aliveColor.blue,
            screenShapeParameters.aliveColor.alpha,
        )
        GLES20.glUniform4f(
            deadColorHandle,
            screenShapeParameters.deadColor.red,
            screenShapeParameters.deadColor.green,
            screenShapeParameters.deadColor.blue,
            screenShapeParameters.deadColor.alpha,
        )
        GLES20.glUniform2i(
            cellWindowSizeHandle,
            screenShapeParameters.cellWindowSize.width,
            screenShapeParameters.cellWindowSize.height,
        )
        GLES20.glUniform1f(scaledCellPixelSizeHandle, screenShapeParameters.scaledCellPixelSize)
        GLES20.glUniform2f(
            pixelOffsetFromCenterHandle,
            screenShapeParameters.pixelOffsetFromCenter.x,
            screenShapeParameters.pixelOffsetFromCenter.y,
        )
        when (screenShapeParameters) {
            is ScreenShapeParameters.RoundRectangle -> {
                GLES20.glUniform1i(shapeTypeHandle, 0)
                GLES20.glUniform1f(sizeFractionHandle, screenShapeParameters.sizeFraction)
                GLES20.glUniform1f(cornerFractionHandle, screenShapeParameters.cornerFraction)
            }
        }
    }

    fun draw(mvpMatrix: FloatArray) {
        GLES20.glUseProgram(program)

        GLES20.glEnableVertexAttribArray(positionHandle)

        GLES20.glVertexAttribPointer(
            positionHandle,
            coordsPerVertex,
            GLES20.GL_FLOAT,
            false,
            vertexStride,
            vertexBuffer,
        )

        GLES20.glUniformMatrix4fv(mvpMatrixHandle, 1, false, mvpMatrix, 0)

        GLES20.glDrawElements(
            GLES20.GL_TRIANGLES,
            drawOrder.size,
            GLES20.GL_UNSIGNED_SHORT,
            drawListBuffer,
        )

        GLES20.glDisableVertexAttribArray(positionHandle)
    }
}

private fun loadShader(type: Int, shaderCode: String) =
    GLES20.glCreateShader(type).apply {
        GLES20.glShaderSource(this, shaderCode)
        GLES20.glCompileShader(this)
    }
