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

package com.alexvanyo.composelife.ui.settings.resources

import com.alexvanyo.composelife.parameterizedstring.ParameterizedString

object Strings

internal expect val Strings.Settings: ParameterizedString

internal expect val Strings.OpenInSettings: ParameterizedString

internal expect val Strings.RemoveSettingFromQuickAccess: ParameterizedString

internal expect val Strings.AddSettingToQuickAccess: ParameterizedString

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

internal expect val Strings.Back: ParameterizedString

internal expect val Strings.Algorithm: ParameterizedString

internal expect val Strings.FeatureFlags: ParameterizedString

internal expect val Strings.Visual: ParameterizedString

internal expect val Strings.ClipboardWatchingOnboardingCompleted: ParameterizedString

internal expect val Strings.EnableClipboardWatching: ParameterizedString
