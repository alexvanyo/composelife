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

internal expect val Strings.DisableAutofit: ParameterizedString

internal expect val Strings.EnableAutofit: ParameterizedString
