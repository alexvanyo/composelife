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

package com.alexvanyo.composelife.ui.app.resources

import com.alexvanyo.composelife.parameterizedstring.ParameterizedString

internal actual fun Strings.TargetStepsPerSecondLabelAndValue(targetStepsPerSecond: Double): ParameterizedString =
    ParameterizedString("Target steps per second: %.2f".format(targetStepsPerSecond))

internal actual fun Strings.TargetStepsPerSecondValue(targetStepsPerSecond: Double): ParameterizedString =
    ParameterizedString("%.2f".format(targetStepsPerSecond))

internal actual val Strings.TargetStepsPerSecondLabel: ParameterizedString get() =
    ParameterizedString("Target steps per second")

internal actual fun Strings.GenerationsPerStepLabelAndValue(generationsPerStep: Int): ParameterizedString =
    ParameterizedString("Generations per step: $generationsPerStep")

internal actual fun Strings.GenerationsPerStepValue(generationsPerStep: Int): ParameterizedString =
    ParameterizedString("$generationsPerStep")

internal actual val Strings.GenerationsPerStepLabel: ParameterizedString get() =
    ParameterizedString("Generations per step")

internal actual fun Strings.InteractableCellContentDescription(x: Int, y: Int): ParameterizedString =
    ParameterizedString("$x, $y")

internal actual fun Strings.OffsetInfoMessage(x: Float, y: Float): ParameterizedString =
    ParameterizedString("Offset: x = %.1f, y = %.1f".format(x, y))

internal actual fun Strings.ScaleInfoMessage(scale: Float): ParameterizedString =
    ParameterizedString("Scale: %.2f".format(scale))

internal actual val Strings.PausedMessage: ParameterizedString get() =
    ParameterizedString("Paused")

internal actual fun Strings.GenerationsPerSecondShortMessage(generationsPerSecond: Double): ParameterizedString =
    ParameterizedString("GPS: %.2f".format(generationsPerSecond))

internal actual fun Strings.GenerationsPerSecondLongMessage(generationsPerSecond: Double): ParameterizedString =
    ParameterizedString("Generations per second: %.2f".format(generationsPerSecond))

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

internal actual val Strings.DisableAutofit: ParameterizedString get() =
    ParameterizedString("Disable autofit")

internal actual val Strings.EnableAutofit: ParameterizedString get() =
    ParameterizedString("Enable autofit")

internal actual val Strings.Speed: ParameterizedString get() =
    ParameterizedString("Speed")

internal actual val Strings.Edit: ParameterizedString get() =
    ParameterizedString("Edit")

internal actual val Strings.Settings: ParameterizedString get() =
    ParameterizedString("Settings")

internal actual val Strings.OpenInSettings: ParameterizedString get() =
    ParameterizedString("Open in settings")

internal actual val Strings.RemoveSettingFromQuickAccess: ParameterizedString get() =
    ParameterizedString("Remove setting from quick access")

internal actual val Strings.AddSettingToQuickAccess: ParameterizedString get() =
    ParameterizedString("Add setting to quick access")
