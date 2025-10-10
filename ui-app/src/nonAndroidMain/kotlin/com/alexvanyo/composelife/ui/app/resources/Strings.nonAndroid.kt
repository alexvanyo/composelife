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
@file:Suppress("TooManyFunctions")

package com.alexvanyo.composelife.ui.app.resources

import com.alexvanyo.composelife.parameterizedstring.ParameterizedString
import com.alexvanyo.composelife.parameterizedstring.ParameterizedStringArgument

internal actual fun Strings.TargetStepsPerSecondLabelAndValue(targetStepsPerSecond: Double): ParameterizedString =
    ParameterizedString("Target steps per second: %.2f", ParameterizedStringArgument(targetStepsPerSecond))

internal actual fun Strings.TargetStepsPerSecondValue(targetStepsPerSecond: Double): ParameterizedString =
    ParameterizedString("%.2f", ParameterizedStringArgument(targetStepsPerSecond))

internal actual val Strings.TargetStepsPerSecondLabel: ParameterizedString get() =
    ParameterizedString("Target steps per second")

internal actual fun Strings.GenerationsPerStepLabelAndValue(generationsPerStep: Int): ParameterizedString =
    ParameterizedString("Generations per step: $generationsPerStep")

internal actual fun Strings.GenerationsPerStepValue(generationsPerStep: Int): ParameterizedString =
    ParameterizedString("$generationsPerStep")

internal actual val Strings.GenerationsPerStepLabel: ParameterizedString get() =
    ParameterizedString("Generations per step")

internal actual fun Strings.OffsetInfoMessage(x: Float, y: Float): ParameterizedString =
    ParameterizedString("Offset: x = %.1f, y = %.1f", ParameterizedStringArgument(x), ParameterizedStringArgument(y))

internal actual fun Strings.ScaleInfoMessage(scale: Float): ParameterizedString =
    ParameterizedString("Scale: %.2f", ParameterizedStringArgument(scale))

internal actual val Strings.PausedMessage: ParameterizedString get() =
    ParameterizedString("Paused")

internal actual fun Strings.GenerationsPerSecondShortMessage(generationsPerSecond: Double): ParameterizedString =
    ParameterizedString("GPS: %.2f", ParameterizedStringArgument(generationsPerSecond))

internal actual fun Strings.GenerationsPerSecondLongMessage(generationsPerSecond: Double): ParameterizedString =
    ParameterizedString("Generations per second: %.2f", ParameterizedStringArgument(generationsPerSecond))

internal actual val Strings.Collapse: ParameterizedString get() =
    ParameterizedString("Collapse")

internal actual val Strings.Expand: ParameterizedString get() =
    ParameterizedString("Expand")

internal actual val Strings.Pause: ParameterizedString get() =
    ParameterizedString("Pause")

internal actual val Strings.Play: ParameterizedString get() =
    ParameterizedString("Play")

internal actual val Strings.Step: ParameterizedString get() =
    ParameterizedString("Step")

internal actual val Strings.ClearSelection: ParameterizedString get() =
    ParameterizedString("Clear selection")

internal actual val Strings.Copy: ParameterizedString get() =
    ParameterizedString("Copy")

internal actual val Strings.Cut: ParameterizedString get() =
    ParameterizedString("Cut")

internal actual val Strings.Paste: ParameterizedString get() =
    ParameterizedString("Paste")

internal actual val Strings.CancelPaste: ParameterizedString get() =
    ParameterizedString("Cancel paste")

internal actual val Strings.ApplyPaste: ParameterizedString get() =
    ParameterizedString("Apply paste")

internal actual val Strings.DisableAutofit: ParameterizedString get() =
    ParameterizedString("Disable autofit")

internal actual val Strings.EnableAutofit: ParameterizedString get() =
    ParameterizedString("Enable autofit")

internal actual val Strings.DisableImmersiveMode: ParameterizedString get() =
    ParameterizedString("Disable immersive mode")

internal actual val Strings.EnableImmersiveMode: ParameterizedString get() =
    ParameterizedString("Enable immersive mode")

internal actual val Strings.EnterHomeSpaceMode: ParameterizedString get() =
    ParameterizedString("Enter home space")

internal actual val Strings.EnterFullSpaceMode: ParameterizedString get() =
    ParameterizedString("Enter full space")

internal actual val Strings.Speed: ParameterizedString get() =
    ParameterizedString("Speed")

internal actual val Strings.Edit: ParameterizedString get() =
    ParameterizedString("Edit")

internal actual val Strings.Settings: ParameterizedString get() =
    ParameterizedString("Settings")

internal actual val Strings.Touch: ParameterizedString get() =
    ParameterizedString("Touch")

internal actual val Strings.TouchTool: ParameterizedString get() =
    ParameterizedString("Touch tool")

internal actual val Strings.Stylus: ParameterizedString get() =
    ParameterizedString("Stylus")

internal actual val Strings.StylusTool: ParameterizedString get() =
    ParameterizedString("Stylus tool")

internal actual val Strings.Mouse: ParameterizedString get() =
    ParameterizedString("Mouse")

internal actual val Strings.MouseTool: ParameterizedString get() =
    ParameterizedString("Mouse tool")

internal actual val Strings.Pan: ParameterizedString get() =
    ParameterizedString("Pan")

internal actual val Strings.Draw: ParameterizedString get() =
    ParameterizedString("Draw")

internal actual val Strings.Erase: ParameterizedString get() =
    ParameterizedString("Erase")

internal actual val Strings.Select: ParameterizedString get() =
    ParameterizedString("Select")

internal actual val Strings.None: ParameterizedString get() =
    ParameterizedString("None")

internal actual val Strings.EmptyClipboard: ParameterizedString get() =
    ParameterizedString("Empty clipboard")

internal actual val Strings.Clipboard: ParameterizedString get() =
    ParameterizedString("Clipboard")

internal actual val Strings.Pinned: ParameterizedString get() =
    ParameterizedString("Pinned")

internal actual val Strings.Pin: ParameterizedString get() =
    ParameterizedString("Pin")

internal actual val Strings.Unpin: ParameterizedString get() =
    ParameterizedString("Unpin")

internal actual val Strings.Back: ParameterizedString get() =
    ParameterizedString("Back")

internal actual val Strings.Close: ParameterizedString get() =
    ParameterizedString("Close")

internal actual val Strings.ClipboardWatchingOnboarding: ParameterizedString get() =
    ParameterizedString(
        "Allow watching the contents of the system clipboard to provide a preview of the cell state? " +
            "This can be changed later in settings.",
    )

internal actual val Strings.Allow: ParameterizedString get() =
    ParameterizedString("Allow")

internal actual val Strings.Disallow: ParameterizedString get() =
    ParameterizedString("Don't allow")

internal actual val Strings.DeserializationSucceeded: ParameterizedString get() =
    ParameterizedString("Deserialization Succeeded")

internal actual val Strings.DeserializationFailed: ParameterizedString get() =
    ParameterizedString("Deserialization Failed")

internal actual val Strings.Warnings: ParameterizedString get() =
    ParameterizedString("Warnings")

internal actual val Strings.Errors: ParameterizedString get() =
    ParameterizedString("Errors")
