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

import com.github.takahirom.roborazzi.CaptureResult
import com.github.takahirom.roborazzi.ExperimentalRoborazziApi
import com.github.takahirom.roborazzi.RoborazziOptions
import com.github.takahirom.roborazzi.RoborazziTaskType
import java.io.File

@OptIn(ExperimentalRoborazziApi::class)
class HashCaptureResultReporter(private val delegate: RoborazziOptions.CaptureResultReporter) :
    RoborazziOptions.CaptureResultReporter {
    override fun report(captureResult: CaptureResult, roborazziTaskType: RoborazziTaskType) {
        when (captureResult) {
            is CaptureResult.Recorded -> handleRecorded(captureResult, roborazziTaskType)
            is CaptureResult.Added -> handleAdded(captureResult, roborazziTaskType)
            is CaptureResult.Unchanged -> handleUnchanged(captureResult, roborazziTaskType)
            else -> delegate.report(captureResult, roborazziTaskType)
        }
    }

    private fun handleRecorded(captureResult: CaptureResult.Recorded, roborazziTaskType: RoborazziTaskType) {
        val goldenFile = File(captureResult.goldenFile)
        val hashFile = File("${goldenFile.path}.sha256")
        val hash = Sha256ImageHash.calculate(goldenFile)
        Sha256ImageHash.writeHash(hashFile, hash)
        delegate.report(captureResult, roborazziTaskType)
    }

    private fun handleAdded(captureResult: CaptureResult.Added, roborazziTaskType: RoborazziTaskType) {
        val goldenFile = File(captureResult.goldenFile)
        val hashFile = File("${goldenFile.path}.sha256")
        val expectedHash = Sha256ImageHash.readHash(hashFile)
            ?: throw AssertionError("Golden image and hash file are missing: ${hashFile.path}")
        val actualFile = File(captureResult.actualFile)
        val actualHash = Sha256ImageHash.calculate(actualFile)
        if (actualHash == expectedHash) {
            delegate.report(
                CaptureResult.Unchanged(
                    goldenFile = captureResult.goldenFile,
                    timestampNs = captureResult.timestampNs,
                    contextData = captureResult.contextData,
                ),
                roborazziTaskType,
            )
        } else {
            throw AssertionError(
                "Screenshot hash mismatch for ${goldenFile.name}!\n" +
                    "Expected: $expectedHash\n" +
                    "Actual:   $actualHash\n" +
                    "Actual image written to: ${actualFile.absolutePath}",
            )
        }
    }

    private fun handleUnchanged(captureResult: CaptureResult.Unchanged, roborazziTaskType: RoborazziTaskType) {
        val goldenFile = File(captureResult.goldenFile)
        val hashFile = File("${goldenFile.path}.sha256")
        val expectedHash = Sha256ImageHash.readHash(hashFile)
        if (expectedHash != null && goldenFile.exists()) {
            val actualHash = Sha256ImageHash.calculate(goldenFile)
            if (actualHash != expectedHash) {
                throw AssertionError(
                    "Local golden image does not match golden hash for ${goldenFile.name}!\n" +
                        "Expected: $expectedHash\n" +
                        "Actual:   $actualHash",
                )
            }
        }
        delegate.report(captureResult, roborazziTaskType)
    }
}
