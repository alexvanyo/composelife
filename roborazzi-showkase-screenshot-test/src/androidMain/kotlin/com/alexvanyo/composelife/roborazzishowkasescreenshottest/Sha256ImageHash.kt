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

import java.io.File
import java.security.MessageDigest
import java.util.Locale

object Sha256ImageHash {
    fun calculate(file: File): String = calculate(file.readBytes())

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
