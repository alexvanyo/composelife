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

internal expect fun Strings.InteractableCellContentDescription(
    x: Int,
    y: Int,
): ParameterizedString

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

internal expect val Strings.Copy: ParameterizedString

internal expect val Strings.Cut: ParameterizedString

internal expect val Strings.Paste: ParameterizedString

internal expect val Strings.CancelPaste: ParameterizedString

internal expect val Strings.ApplyPaste: ParameterizedString

internal expect val Strings.DisableAutofit: ParameterizedString

internal expect val Strings.EnableAutofit: ParameterizedString

internal expect val Strings.Speed: ParameterizedString

internal expect val Strings.Edit: ParameterizedString

internal expect val Strings.Settings: ParameterizedString

internal expect val Strings.OpenInSettings: ParameterizedString

internal expect val Strings.RemoveSettingFromQuickAccess: ParameterizedString

internal expect val Strings.AddSettingToQuickAccess: ParameterizedString

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

internal expect val Strings.AlgorithmImplementation: ParameterizedString

internal expect val Strings.NaiveAlgorithm: ParameterizedString

internal expect val Strings.HashLifeAlgorithm: ParameterizedString

internal expect val Strings.DoNotKeepProcess: ParameterizedString

internal expect val Strings.DisableOpenGL: ParameterizedString

internal expect val Strings.DisableAGSL: ParameterizedString

internal expect val Strings.Shape: ParameterizedString

internal expect fun Strings.SizeFractionLabelAndValue(sizeFraction: Float): ParameterizedString

internal expect fun Strings.SizeFractionValue(sizeFraction: Float): ParameterizedString

internal expect val Strings.SizeFractionLabel: ParameterizedString

internal expect fun Strings.CornerFractionLabelAndValue(cornerFraction: Float): ParameterizedString

internal expect fun Strings.CornerFractionValue(cornerFraction: Float): ParameterizedString

internal expect val Strings.CornerFractionLabel: ParameterizedString

internal expect val Strings.RoundRectangle: ParameterizedString

internal expect val Strings.DarkThemeConfig: ParameterizedString

internal expect val Strings.FollowSystem: ParameterizedString

internal expect val Strings.DarkTheme: ParameterizedString

internal expect val Strings.LightTheme: ParameterizedString

internal expect val Strings.QuickSettingsInfo: ParameterizedString

internal expect val Strings.SeeAll: ParameterizedString
