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

object Strings

internal expect fun Strings.TargetStepsPerSecondLabelAndValue(targetStepsPerSecond: Double): ParameterizedString

internal expect fun Strings.TargetStepsPerSecondValue(targetStepsPerSecond: Double): ParameterizedString

internal expect val Strings.TargetStepsPerSecondLabel: ParameterizedString

internal expect fun Strings.GenerationsPerStepLabelAndValue(generationsPerStep: Int): ParameterizedString

internal expect fun Strings.GenerationsPerStepValue(generationsPerStep: Int): ParameterizedString

internal expect val Strings.GenerationsPerStepLabel: ParameterizedString

internal expect fun Strings.OffsetInfoMessage(x: Float, y: Float): ParameterizedString

internal expect fun Strings.ScaleInfoMessage(scale: Float): ParameterizedString

internal expect val Strings.PausedMessage: ParameterizedString

internal expect fun Strings.GenerationsPerSecondShortMessage(generationsPerSecond: Double): ParameterizedString

internal expect fun Strings.GenerationsPerSecondLongMessage(generationsPerSecond: Double): ParameterizedString

internal expect val Strings.Collapse: ParameterizedString

internal expect val Strings.Expand: ParameterizedString

internal expect val Strings.Pause: ParameterizedString

internal expect val Strings.Play: ParameterizedString

internal expect val Strings.Step: ParameterizedString

internal expect val Strings.ClearSelection: ParameterizedString

internal expect val Strings.Copy: ParameterizedString

internal expect val Strings.Cut: ParameterizedString

internal expect val Strings.Paste: ParameterizedString

internal expect val Strings.CancelPaste: ParameterizedString

internal expect val Strings.ApplyPaste: ParameterizedString

internal expect val Strings.DisableAutofit: ParameterizedString

internal expect val Strings.EnableAutofit: ParameterizedString

internal expect val Strings.DisableImmersiveMode: ParameterizedString

internal expect val Strings.EnableImmersiveMode: ParameterizedString

internal expect val Strings.Speed: ParameterizedString

internal expect val Strings.Edit: ParameterizedString

internal expect val Strings.Settings: ParameterizedString

internal expect val Strings.Touch: ParameterizedString

internal expect val Strings.TouchTool: ParameterizedString

internal expect val Strings.Stylus: ParameterizedString

internal expect val Strings.StylusTool: ParameterizedString

internal expect val Strings.Mouse: ParameterizedString

internal expect val Strings.MouseTool: ParameterizedString

internal expect val Strings.Pan: ParameterizedString

internal expect val Strings.Draw: ParameterizedString

internal expect val Strings.Erase: ParameterizedString

internal expect val Strings.Select: ParameterizedString

internal expect val Strings.None: ParameterizedString

internal expect val Strings.EmptyClipboard: ParameterizedString

internal expect val Strings.Clipboard: ParameterizedString

internal expect val Strings.Pinned: ParameterizedString

internal expect val Strings.Pin: ParameterizedString

internal expect val Strings.Unpin: ParameterizedString

internal expect val Strings.Back: ParameterizedString

internal expect val Strings.Close: ParameterizedString

internal expect val Strings.ClipboardWatchingOnboarding: ParameterizedString

internal expect val Strings.Allow: ParameterizedString

internal expect val Strings.Disallow: ParameterizedString

internal expect val Strings.DeserializationSucceeded: ParameterizedString

internal expect val Strings.DeserializationFailed: ParameterizedString

internal expect val Strings.Warnings: ParameterizedString

internal expect val Strings.Errors: ParameterizedString
