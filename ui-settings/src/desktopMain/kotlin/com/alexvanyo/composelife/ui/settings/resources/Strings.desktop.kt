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

internal actual val Strings.Settings: ParameterizedString get() =
    ParameterizedString("Settings")

internal actual val Strings.OpenInSettings: ParameterizedString get() =
    ParameterizedString("Open in settings")

internal actual val Strings.RemoveSettingFromQuickAccess: ParameterizedString get() =
    ParameterizedString("Remove setting from quick access")

internal actual val Strings.AddSettingToQuickAccess: ParameterizedString get() =
    ParameterizedString("Add setting to quick access")

internal actual val Strings.AlgorithmImplementation: ParameterizedString get() =
    ParameterizedString("Implementation")

internal actual val Strings.NaiveAlgorithm: ParameterizedString get() =
    ParameterizedString("Naïve")

internal actual val Strings.HashLifeAlgorithm: ParameterizedString get() =
    ParameterizedString("Hashlife")

internal actual val Strings.DoNotKeepProcess: ParameterizedString get() =
    ParameterizedString("Do not keep process")

internal actual val Strings.DisableOpenGL: ParameterizedString get() =
    ParameterizedString("Disable OpenGL")

internal actual val Strings.DisableAGSL: ParameterizedString get() =
    ParameterizedString("Disable AGSL")

internal actual val Strings.Shape: ParameterizedString get() =
    ParameterizedString("Shape")

internal actual fun Strings.SizeFractionLabelAndValue(sizeFraction: Float): ParameterizedString =
    ParameterizedString("Size fraction: %.2f", sizeFraction)

internal actual fun Strings.SizeFractionValue(sizeFraction: Float): ParameterizedString =
    ParameterizedString("%.2f", sizeFraction)

internal actual val Strings.SizeFractionLabel: ParameterizedString get() =
    ParameterizedString("Size fraction")

internal actual fun Strings.CornerFractionLabelAndValue(cornerFraction: Float): ParameterizedString =
    ParameterizedString("Corner fraction: %.2f", cornerFraction)

internal actual fun Strings.CornerFractionValue(cornerFraction: Float): ParameterizedString =
    ParameterizedString("%.2f", cornerFraction)

internal actual val Strings.CornerFractionLabel: ParameterizedString get() =
    ParameterizedString("Corner fraction")

internal actual val Strings.RoundRectangle: ParameterizedString get() =
    ParameterizedString("Round Rectangle")

internal actual val Strings.DarkThemeConfig: ParameterizedString get() =
    ParameterizedString("Theme")

internal actual val Strings.FollowSystem: ParameterizedString get() =
    ParameterizedString("Follow system")

internal actual val Strings.DarkTheme: ParameterizedString get() =
    ParameterizedString("Dark")

internal actual val Strings.LightTheme: ParameterizedString get() =
    ParameterizedString("Light")

internal actual val Strings.QuickSettingsInfo: ParameterizedString get() =
    ParameterizedString("Settings saved for quick access will appear here")

internal actual val Strings.SeeAll: ParameterizedString get() =
    ParameterizedString("See all…")

internal actual val Strings.Back: ParameterizedString get() =
    ParameterizedString("Back")

internal actual val Strings.Algorithm: ParameterizedString get() =
    ParameterizedString("Algorithm")

internal actual val Strings.FeatureFlags: ParameterizedString get() =
    ParameterizedString("Feature flags")

internal actual val Strings.Visual: ParameterizedString get() =
    ParameterizedString("Visual")

internal actual val Strings.ClipboardWatchingOnboardingCompleted: ParameterizedString get() =
    ParameterizedString("Watch clipboard onboarding completed")

internal actual val Strings.EnableClipboardWatching: ParameterizedString get() =
    ParameterizedString("Enable clipboard watching")
