/*
 * Copyright 2023 The Android Open Source Project
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

package com.alexvanyo.composelife.wear

import android.graphics.Bitmap
import android.graphics.Canvas
import android.graphics.Color
import android.opengl.GLES20
import android.opengl.GLUtils
import androidx.compose.ui.unit.IntSize
import androidx.compose.ui.unit.toIntRect
import androidx.wear.watchface.ComplicationSlot
import androidx.wear.watchface.RenderParameters
import com.alexvanyo.composelife.openglrenderer.checkOpenGLError
import com.alexvanyo.composelife.openglrenderer.getTextureReference
import com.alexvanyo.composelife.openglrenderer.loadShader
import org.intellij.lang.annotations.Language
import java.nio.ByteBuffer
import java.nio.ByteOrder
import java.nio.FloatBuffer
import java.nio.ShortBuffer
import java.time.ZonedDateTime

@Language("GLSL")
private val vertexShaderCode = """
    uniform mat4 mvpMatrix;
    attribute vec4 position;
    attribute vec4 textureCoordinate;
    varying vec2 textureCoord;
    void main() {
        gl_Position = mvpMatrix * position;
        textureCoord = textureCoordinate.xy;
    }
""".trimIndent()

@Language("GLSL")
private val fragmentShaderCode = """
    // The complication texture
    uniform sampler2D complication;
    varying highp vec2 textureCoord;
    void main() {
        gl_FragColor = texture2D(complication, textureCoord);
    }
""".trimIndent()

class ComplicationShape(
    screenSize: IntSize,
    private val complicationSlot: ComplicationSlot,
    private val texture: Int,
) {
    private val bounds = complicationSlot.computeBounds(screenSize.toIntRect().toAndroidRect()).toComposeIntRect()

    private val bitmap = Bitmap.createBitmap(
        bounds.width,
        bounds.height,
        Bitmap.Config.ARGB_8888
    )
    private val canvas = Canvas(bitmap)

    private val coords = floatArrayOf(
        bounds.left.toFloat() / screenSize.width, 1f - (bounds.bottom.toFloat() / screenSize.height), 0f,
        bounds.left.toFloat() / screenSize.width, 1f - (bounds.top.toFloat() / screenSize.height), 0f,
        bounds.right.toFloat() / screenSize.width, 1f - (bounds.top.toFloat() / screenSize.height), 0f,
        bounds.right.toFloat() / screenSize.width, 1f - (bounds.bottom.toFloat() / screenSize.height), 0f,
    )

    private val textureCoords = floatArrayOf(
        0f,
        1f,
        0f,
        0f,
        1f,
        0f,
        1f,
        1f,
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

    private val textureCoordsPerVertex = 2

    private val textureCoordsStride = textureCoordsPerVertex * 4

    private val textureCoordsBuffer: FloatBuffer =
        ByteBuffer.allocateDirect(textureCoords.size * 4).run {
            order(ByteOrder.nativeOrder())
            asFloatBuffer().apply {
                put(textureCoords)
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
    private val textureCoordinateHandle = GLES20.glGetAttribLocation(program, "textureCoordinate")
    private val complicationHandle = GLES20.glGetUniformLocation(program, "complication")
    private val mvpMatrixHandle = GLES20.glGetUniformLocation(program, "mvpMatrix")

    private val textureHandle = run {
        val array = IntArray(1)
        GLES20.glGenTextures(0, array, 0)
        array[0]
    }

    @Suppress("LongMethod")
    fun draw(
        zonedDateTime: ZonedDateTime,
        renderParameters: RenderParameters,
        mvpMatrix: FloatArray
    ) {
        GLES20.glUseProgram(program)
        checkOpenGLError()
        GLES20.glTexParameteri(
            GLES20.GL_TEXTURE_2D,
            GLES20.GL_TEXTURE_WRAP_S,
            GLES20.GL_CLAMP_TO_EDGE
        )
        GLES20.glTexParameteri(
            GLES20.GL_TEXTURE_2D,
            GLES20.GL_TEXTURE_WRAP_T,
            GLES20.GL_CLAMP_TO_EDGE
        )
        GLES20.glTexParameteri(
            GLES20.GL_TEXTURE_2D,
            GLES20.GL_TEXTURE_MAG_FILTER,
            GLES20.GL_LINEAR
        )
        GLES20.glTexParameteri(
            GLES20.GL_TEXTURE_2D,
            GLES20.GL_TEXTURE_MIN_FILTER,
            GLES20.GL_LINEAR
        )
        GLES20.glActiveTexture(getTextureReference(texture))
        GLES20.glBindTexture(GLES20.GL_TEXTURE_2D, textureHandle)

        canvas.drawColor(Color.TRANSPARENT)
        complicationSlot.renderer.render(
            canvas,
            bounds.size.toIntRect().toAndroidRect(),
            zonedDateTime,
            renderParameters,
            complicationSlot.id
        )
        checkOpenGLError()

        GLES20.glPixelStorei(GLES20.GL_UNPACK_ALIGNMENT, 4)
        GLUtils.texImage2D(GLES20.GL_TEXTURE_2D, 0, bitmap, 0)
        checkOpenGLError()

        GLES20.glUniform1i(complicationHandle, texture)
        checkOpenGLError()

        GLES20.glEnableVertexAttribArray(positionHandle)
        GLES20.glEnableVertexAttribArray(textureCoordinateHandle)

        GLES20.glVertexAttribPointer(
            positionHandle,
            coordsPerVertex,
            GLES20.GL_FLOAT,
            false,
            vertexStride,
            vertexBuffer,
        )

        GLES20.glVertexAttribPointer(
            textureCoordinateHandle,
            textureCoordsPerVertex,
            GLES20.GL_FLOAT,
            false,
            textureCoordsStride,
            textureCoordsBuffer,
        )

        GLES20.glUniformMatrix4fv(mvpMatrixHandle, 1, false, mvpMatrix, 0)

        GLES20.glDrawElements(
            GLES20.GL_TRIANGLES,
            drawOrder.size,
            GLES20.GL_UNSIGNED_SHORT,
            drawListBuffer,
        )

        GLES20.glDisableVertexAttribArray(positionHandle)
        GLES20.glDisableVertexAttribArray(textureCoordinateHandle)
        checkOpenGLError()
    }
}
