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

import android.app.ActivityManager
import android.opengl.EGLConfig
import android.opengl.EGLSurface
import android.opengl.GLES20
import android.opengl.Matrix
import android.view.Surface
import androidx.compose.foundation.AndroidExternalSurface
import androidx.compose.foundation.AndroidExternalSurfaceZOrder
import androidx.compose.runtime.Composable
import androidx.compose.runtime.RememberObserver
import androidx.compose.runtime.getValue
import androidx.compose.runtime.remember
import androidx.compose.runtime.rememberUpdatedState
import androidx.compose.runtime.snapshotFlow
import androidx.compose.ui.Modifier
import androidx.compose.ui.geometry.Offset
import androidx.compose.ui.platform.LocalContext
import androidx.compose.ui.platform.LocalDensity
import androidx.compose.ui.unit.Dp
import androidx.core.content.getSystemService
import androidx.graphics.opengl.GLRenderer
import androidx.graphics.opengl.egl.EGLManager
import androidx.graphics.opengl.egl.EGLSpec
import com.alexvanyo.composelife.model.CellWindow
import com.alexvanyo.composelife.model.GameOfLifeState
import com.alexvanyo.composelife.openglrenderer.GameOfLifeShape
import com.alexvanyo.composelife.openglrenderer.GameOfLifeShapeParameters
import com.alexvanyo.composelife.preferences.CurrentShape
import com.alexvanyo.composelife.ui.app.theme.ComposeLifeTheme
import kotlinx.coroutines.flow.collect
import kotlinx.coroutines.flow.onEach
import java.nio.IntBuffer

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
    cellWindow: CellWindow,
    shape: CurrentShape,
    pixelOffsetFromCenter: Offset,
    modifier: Modifier = Modifier,
    inOverlay: Boolean = false,
) {
    val scaledCellPixelSize = with(LocalDensity.current) { scaledCellDpSize.toPx() }

    val aliveColor = ComposeLifeTheme.aliveCellColor
    val deadColor = ComposeLifeTheme.deadCellColor

    val cellsBuffer = remember(cellWindow, gameOfLifeState.cellState) {
        val buffer = IntBuffer.allocate(cellWindow.width * cellWindow.height)

        gameOfLifeState.cellState.getAliveCellsInWindow(cellWindow).forEach { cell ->
            val index = (cellWindow.bottom - 1 - cell.y) * cellWindow.width +
                cell.x - cellWindow.left
            buffer.put(index, android.graphics.Color.WHITE)
        }

        buffer
    }

    val parameters by rememberUpdatedState(
        when (shape) {
            is CurrentShape.RoundRectangle -> {
                GameOfLifeShapeParameters.RoundRectangle(
                    cells = cellsBuffer,
                    aliveColor = aliveColor,
                    deadColor = deadColor,
                    cellWindowSize = cellWindow.size,
                    scaledCellPixelSize = scaledCellPixelSize,
                    pixelOffsetFromCenter = pixelOffsetFromCenter,
                    sizeFraction = shape.sizeFraction,
                    cornerFraction = shape.cornerFraction,
                )
            }
        },
    )

    val glRenderer = rememberGLRenderer()

    AndroidExternalSurface(
        modifier = modifier,
        zOrder = if (inOverlay) {
            AndroidExternalSurfaceZOrder.MediaOverlay
        } else {
            AndroidExternalSurfaceZOrder.Behind
        },
    ) {
        onSurface { surface, width, height ->
            val renderTarget = glRenderer.attach(
                surface,
                width,
                height,
                object : GLRenderer.RenderCallback {
                    private lateinit var gameOfLifeShape: GameOfLifeShape

                    private val mvpMatrix = FloatArray(16)

                    init {
                        val projectionMatrix = FloatArray(16)
                        Matrix.orthoM(projectionMatrix, 0, 0f, 1f, 0f, 1f, 0.5f, 2f)
                        val viewMatrix = FloatArray(16)
                        Matrix.setLookAtM(viewMatrix, 0, 0f, 0f, 1f, 0f, 0f, 0f, 0f, 1f, 0f)
                        Matrix.multiplyMM(mvpMatrix, 0, projectionMatrix, 0, viewMatrix, 0)
                    }

                    override fun onSurfaceCreated(
                        spec: EGLSpec,
                        config: EGLConfig,
                        surface: Surface,
                        width: Int,
                        height: Int,
                    ): EGLSurface? {
                        return super.onSurfaceCreated(spec, config, surface, width, height).also {
                            GLES20.glClearColor(0f, 0f, 0f, 0f)
                            GLES20.glViewport(0, 0, width, height)
                            gameOfLifeShape = GameOfLifeShape().apply {
                                setSize(width, height)
                            }
                        }
                    }

                    override fun onDrawFrame(eglManager: EGLManager) {
                        gameOfLifeShape.setScreenShapeParameters(parameters)
                        gameOfLifeShape.draw(mvpMatrix)
                    }
                },
            )

            surface.onChanged { w, h ->
                renderTarget.resize(w, h)
            }

            surface.onDestroyed {
                glRenderer.detach(renderTarget, true)
            }

            snapshotFlow { parameters }
                .onEach {
                    renderTarget.requestRender()
                }
                .collect()
        }
    }
}

@Composable
fun rememberGLRenderer(): GLRenderer =
    remember {
        object : RememberObserver {
            val glRenderer = GLRenderer()
            override fun onAbandoned() = onForgotten()
            override fun onForgotten() {
                glRenderer.stop(true)
            }
            override fun onRemembered() {
                glRenderer.start()
            }
        }
    }.glRenderer
