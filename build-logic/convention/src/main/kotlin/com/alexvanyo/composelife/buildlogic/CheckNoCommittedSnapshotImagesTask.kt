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

package com.alexvanyo.composelife.buildlogic

import org.gradle.api.DefaultTask
import org.gradle.api.GradleException
import org.gradle.api.tasks.TaskAction
import org.gradle.process.ExecOperations
import org.gradle.work.DisableCachingByDefault
import java.io.ByteArrayOutputStream
import javax.inject.Inject

@DisableCachingByDefault(because = "Runs a fast git index check")
abstract class CheckNoCommittedSnapshotImagesTask : DefaultTask() {

    @get:Inject
    abstract val execOperations: ExecOperations

    @TaskAction
    fun check() {
        val outputStream = ByteArrayOutputStream()
        execOperations.exec {
            commandLine("git", "ls-files", "**/snapshots/*.png")
            standardOutput = outputStream
        }
        val output = outputStream.toString(Charsets.UTF_8).trim()
        if (output.isNotEmpty()) {
            throw GradleException(
                "Found committed snapshot PNG files in Git:\n$output\n" +
                    "Roborazzi golden images must only be stored as .sha256 hash files!",
            )
        }
    }
}
