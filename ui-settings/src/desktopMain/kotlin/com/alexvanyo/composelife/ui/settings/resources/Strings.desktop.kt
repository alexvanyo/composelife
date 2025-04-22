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
import com.alexvanyo.composelife.parameterizedstring.ParameterizedStringArgument

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
    ParameterizedString("Size fraction: %.2f", ParameterizedStringArgument(sizeFraction))

internal actual fun Strings.SizeFractionValue(sizeFraction: Float): ParameterizedString =
    ParameterizedString("%.2f", ParameterizedStringArgument(sizeFraction))

internal actual val Strings.SizeFractionLabel: ParameterizedString get() =
    ParameterizedString("Size fraction")

internal actual fun Strings.CornerFractionLabelAndValue(cornerFraction: Float): ParameterizedString =
    ParameterizedString("Corner fraction: %.2f", ParameterizedStringArgument(cornerFraction))

internal actual fun Strings.CornerFractionValue(cornerFraction: Float): ParameterizedString =
    ParameterizedString("%.2f", ParameterizedStringArgument(cornerFraction))

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
    ParameterizedString("Feature Flags")

internal actual val Strings.PatternCollections: ParameterizedString get() =
    ParameterizedString("Pattern Collections")

internal actual val Strings.Visual: ParameterizedString get() =
    ParameterizedString("Visual")

internal actual val Strings.ClipboardWatchingOnboardingCompleted: ParameterizedString get() =
    ParameterizedString("Watch clipboard onboarding completed")

internal actual val Strings.EnableClipboardWatching: ParameterizedString get() =
    ParameterizedString("Enable clipboard watching")

internal actual val Strings.Delete: ParameterizedString get() =
    ParameterizedString("Delete")

internal actual val Strings.SynchronizePatternCollectionsOnMeteredNetwork: ParameterizedString get() =
    ParameterizedString("Synchronize pattern collections on metered network")

internal actual val Strings.PatternCollectionsSynchronizationPeriod: ParameterizedString get() =
    ParameterizedString("Pattern collect synchronization period")

internal actual fun Strings.PatternCollectionsSynchronizationPeriodLabelAndValue(period: Double): ParameterizedString =
    ParameterizedString("Period in minutes: %.1f", ParameterizedStringArgument(period))

internal actual fun Strings.PatternCollectionsSynchronizationPeriodValue(period: Double): ParameterizedString =
    ParameterizedString("%.1f", ParameterizedStringArgument(period))

internal actual val Strings.PatternCollectionsSynchronizationPeriodSuffix: ParameterizedString get() =
    ParameterizedString("minutes")

internal actual val Strings.AddPatternCollection: ParameterizedString get() =
    ParameterizedString("Add pattern collection source")

internal actual val Strings.LastSuccessfulSync: ParameterizedString get() =
    ParameterizedString("Last successful sync:")

internal actual val Strings.LastUnsuccessfulSync: ParameterizedString get() =
    ParameterizedString("Last unsuccessful sync:")

internal actual val Strings.DayUnit: ParameterizedString get() =
    ParameterizedString("day(s)")

internal actual val Strings.HourUnit: ParameterizedString get() =
    ParameterizedString("hour(s)")

internal actual val Strings.MinuteUnit: ParameterizedString get() =
    ParameterizedString("minute(s)")

internal actual val Strings.SecondUnit: ParameterizedString get() =
    ParameterizedString("second(s)")

internal actual val Strings.Never: ParameterizedString get() =
    ParameterizedString("Never")

internal actual val Strings.Sources: ParameterizedString get() =
    ParameterizedString("Sources")

internal actual val Strings.SourceUrlLabel: ParameterizedString get() =
    ParameterizedString("Source URL")

internal actual val Strings.EnableWindowShapeClipping: ParameterizedString get() =
    ParameterizedString("Enable window shape clipping")
