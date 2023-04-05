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

package com.alexvanyo.composelife.openglrenderer

import android.opengl.GLES20
import androidx.annotation.IntRange

/**
 * Throws if there has been an OpenGL error.
 */
fun checkOpenGLError() {
    val error = GLES20.glGetError()
    if (error != GLES20.GL_NO_ERROR) {
        error("OpenGL error: $error")
    }
}

/**
 * Creates and compiles the given [shaderCode] of type [type].
 */
fun loadShader(type: Int, shaderCode: String): Int =
    GLES20.glCreateShader(type).apply {
        GLES20.glShaderSource(this, shaderCode)
        GLES20.glCompileShader(this)
    }

/**
 * Converts an [index] into the corresponding [GLES20.GL_TEXTURE0] reference, from [GLES20.GL_TEXTURE0] to
 * [GLES20.GL_TEXTURE31].
 */
@Suppress("CyclomaticComplexMethod")
fun getTextureReference(
    @IntRange(from = 0, to = 31) index: Int,
): Int =
    when (index) {
        0 -> GLES20.GL_TEXTURE0
        1 -> GLES20.GL_TEXTURE1
        2 -> GLES20.GL_TEXTURE2
        3 -> GLES20.GL_TEXTURE3
        4 -> GLES20.GL_TEXTURE4
        5 -> GLES20.GL_TEXTURE5
        6 -> GLES20.GL_TEXTURE6
        7 -> GLES20.GL_TEXTURE7
        8 -> GLES20.GL_TEXTURE8
        9 -> GLES20.GL_TEXTURE9
        10 -> GLES20.GL_TEXTURE10
        11 -> GLES20.GL_TEXTURE11
        12 -> GLES20.GL_TEXTURE12
        13 -> GLES20.GL_TEXTURE13
        14 -> GLES20.GL_TEXTURE14
        15 -> GLES20.GL_TEXTURE15
        16 -> GLES20.GL_TEXTURE16
        17 -> GLES20.GL_TEXTURE17
        18 -> GLES20.GL_TEXTURE18
        19 -> GLES20.GL_TEXTURE19
        20 -> GLES20.GL_TEXTURE20
        21 -> GLES20.GL_TEXTURE21
        22 -> GLES20.GL_TEXTURE22
        23 -> GLES20.GL_TEXTURE23
        24 -> GLES20.GL_TEXTURE24
        25 -> GLES20.GL_TEXTURE25
        26 -> GLES20.GL_TEXTURE26
        27 -> GLES20.GL_TEXTURE27
        28 -> GLES20.GL_TEXTURE28
        29 -> GLES20.GL_TEXTURE29
        30 -> GLES20.GL_TEXTURE30
        31 -> GLES20.GL_TEXTURE31
        else -> throw IllegalArgumentException("Invalid index!")
    }
