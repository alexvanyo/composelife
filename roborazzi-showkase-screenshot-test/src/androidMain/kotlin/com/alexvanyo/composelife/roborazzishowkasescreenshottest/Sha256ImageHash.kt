/*
 * Copyright 2026 The Android Open Source Project
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

package com.alexvanyo.composelife.roborazzishowkasescreenshottest

import android.graphics.Bitmap
import android.graphics.BitmapFactory
import java.io.File
import java.nio.ByteBuffer
import java.nio.ByteOrder
import java.security.MessageDigest
import java.util.Locale

object Sha256ImageHash {
    fun calculate(file: File): String {
        val options = BitmapFactory.Options().apply {
            inPreferredConfig = Bitmap.Config.ARGB_8888
            inPremultiplied = false
            inScaled = false
        }
        val bitmap = requireNotNull(BitmapFactory.decodeFile(file.absolutePath, options)) {
            "Failed to decode image file: ${file.absolutePath}"
        }
        try {
            return calculate(bitmap)
        } finally {
            bitmap.recycle()
        }
    }

    fun calculate(bitmap: Bitmap): String {
        val width = bitmap.width
        val height = bitmap.height
        val pixels = IntArray(width * height)
        bitmap.getPixels(pixels, 0, width, 0, 0, width, height)

        val buffer = ByteBuffer.allocate(Int.SIZE_BYTES * 2 + pixels.size * Int.SIZE_BYTES)
            .order(ByteOrder.BIG_ENDIAN)
        buffer.putInt(width)
        buffer.putInt(height)
        buffer.asIntBuffer().put(pixels)
        return calculate(buffer.array())
    }

    fun calculate(bytes: ByteArray): String {
        val digest = MessageDigest.getInstance("SHA-256")
        val hashBytes = digest.digest(bytes)
        return hashBytes.joinToString("") { "%02x".format(Locale.ROOT, it) }
    }

    fun readHash(hashFile: File): String? {
        if (!hashFile.exists()) return null
        return hashFile.readText().trim().split(Regex("\\s+")).firstOrNull()
    }

    fun writeHash(hashFile: File, hash: String) {
        hashFile.parentFile?.mkdirs()
        hashFile.writeText("$hash\n")
    }
}
