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
import androidx.compose.ui.platform.LocalContext
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.platform.LocalLifecycleOwner
import androidx.compose.ui.unit.Dp
import androidx.compose.ui.unit.IntRect
import androidx.compose.ui.unit.IntSize
import androidx.compose.ui.viewinterop.AndroidView
import androidx.core.content.getSystemService
import androidx.lifecycle.Lifecycle
import androidx.lifecycle.repeatOnLifecycle
import com.alexvanyo.composelife.model.GameOfLifeState
import com.alexvanyo.composelife.openglrenderer.GameOfLifeShape
import com.alexvanyo.composelife.openglrenderer.GameOfLifeShapeParameters
import com.alexvanyo.composelife.preferences.CurrentShape
import com.alexvanyo.composelife.ui.theme.ComposeLifeTheme
import kotlinx.coroutines.asCoroutineDispatcher
import kotlinx.coroutines.awaitCancellation
import kotlinx.coroutines.flow.MutableStateFlow
import kotlinx.coroutines.flow.collect
import kotlinx.coroutines.flow.flowOn
import kotlinx.coroutines.flow.onEach
import kotlinx.coroutines.launch
import java.nio.IntBuffer
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

@Suppress("LongParameterList", "LongMethod")
@Composable
fun OpenGLNonInteractableCells(
    gameOfLifeState: GameOfLifeState,
    scaledCellDpSize: Dp,
    cellWindow: IntRect,
    shape: CurrentShape,
    pixelOffsetFromCenter: Offset,
    modifier: Modifier = Modifier,
    inOverlay: Boolean = false,
) {
    val scaledCellPixelSize = with(LocalDensity.current) { scaledCellDpSize.toPx() }

    val aliveColor = ComposeLifeTheme.aliveCellColor
    val deadColor = ComposeLifeTheme.deadCellColor

    val cellWindowSize = remember(cellWindow) {
        IntSize(cellWindow.width + 1, cellWindow.height + 1)
    }

    val cellsBuffer = remember(cellWindow, cellWindowSize, gameOfLifeState.cellState) {
        val buffer = IntBuffer.allocate(cellWindowSize.width * cellWindowSize.height)

        gameOfLifeState.cellState.getAliveCellsInWindow(cellWindow).forEach { cell ->
            val index = (cellWindow.bottom - cell.y) * cellWindowSize.width + cell.x - cellWindow.left
            buffer.put(index, android.graphics.Color.WHITE)
        }

        buffer
    }

    val parameters = when (shape) {
        is CurrentShape.RoundRectangle -> {
            GameOfLifeShapeParameters.RoundRectangle(
                cells = cellsBuffer,
                aliveColor = aliveColor,
                deadColor = deadColor,
                cellWindowSize = cellWindowSize,
                scaledCellPixelSize = scaledCellPixelSize,
                pixelOffsetFromCenter = pixelOffsetFromCenter,
                sizeFraction = shape.sizeFraction,
                cornerFraction = shape.cornerFraction,
            )
        }
    }

    val lifecycleOwner = LocalLifecycleOwner.current
    val coroutineScope = rememberCoroutineScope()

    AndroidView(
        factory = { context ->
            object : GLSurfaceView(context) {
                val parametersState = MutableStateFlow(parameters)

                val renderer = object : Renderer {
                    private val mvpMatrix = FloatArray(16)

                    init {
                        val projectionMatrix = FloatArray(16)
                        Matrix.orthoM(projectionMatrix, 0, 0f, 1f, 0f, 1f, 0.5f, 2f)
                        val viewMatrix = FloatArray(16)
                        Matrix.setLookAtM(viewMatrix, 0, 0f, 0f, 1f, 0f, 0f, 0f, 0f, 1f, 0f)
                        Matrix.multiplyMM(mvpMatrix, 0, projectionMatrix, 0, viewMatrix, 0)
                    }

                    lateinit var gameOfLifeShape: GameOfLifeShape

                    override fun onSurfaceCreated(unused: GL10?, config: EGLConfig?) {
                        GLES20.glClearColor(0f, 0f, 0f, 0f)
                        gameOfLifeShape = GameOfLifeShape()
                        gameOfLifeShape.setScreenShapeParameters(parametersState.value)
                    }

                    override fun onSurfaceChanged(unused: GL10?, width: Int, height: Int) {
                        GLES20.glViewport(0, 0, width, height)
                        gameOfLifeShape.setSize(width, height)
                    }

                    override fun onDrawFrame(unused: GL10?) {
                        gameOfLifeShape.draw(mvpMatrix)
                    }

                    fun setParameters(parameters: GameOfLifeShapeParameters) {
                        if (::gameOfLifeShape.isInitialized) {
                            gameOfLifeShape.setScreenShapeParameters(parameters)
                        }
                    }
                }
            }.apply {
                setEGLContextClientVersion(2)
                setRenderer(renderer)
                renderMode = GLSurfaceView.RENDERMODE_WHEN_DIRTY

                val openGLExecutor = Executor(::queueEvent)
                val openGLDispatcher = openGLExecutor.asCoroutineDispatcher()

                coroutineScope.launch {
                    parametersState
                        .onEach(renderer::setParameters)
                        .onEach { requestRender() }
                        .flowOn(openGLDispatcher)
                        .collect()
                }

                coroutineScope.launch {
                    lifecycleOwner.repeatOnLifecycle(Lifecycle.State.STARTED) {
                        onResume()
                        try {
                            awaitCancellation()
                        } finally {
                            onPause()
                        }
                    }
                }
            }
        },
        update = {
            it.parametersState.value = parameters
            it.setZOrderMediaOverlay(inOverlay)
        },
        modifier = modifier,
    )
}
