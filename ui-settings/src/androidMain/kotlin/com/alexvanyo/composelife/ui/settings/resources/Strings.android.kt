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
import com.alexvanyo.composelife.ui.settings.R

internal actual val Strings.Settings: ParameterizedString get() =
    ParameterizedString(R.string.settings)

internal actual val Strings.OpenInSettings: ParameterizedString get() =
    ParameterizedString(R.string.open_in_settings)

internal actual val Strings.RemoveSettingFromQuickAccess: ParameterizedString get() =
    ParameterizedString(R.string.remove_setting_from_quick_access)

internal actual val Strings.AddSettingToQuickAccess: ParameterizedString get() =
    ParameterizedString(R.string.add_setting_to_quick_access)

internal actual val Strings.AlgorithmImplementation: ParameterizedString get() =
    ParameterizedString(R.string.algorithm_implementation)

internal actual val Strings.NaiveAlgorithm: ParameterizedString get() =
    ParameterizedString(R.string.naive_algorithm)

internal actual val Strings.HashLifeAlgorithm: ParameterizedString get() =
    ParameterizedString(R.string.hash_life_algorithm)

internal actual val Strings.DoNotKeepProcess: ParameterizedString get() =
    ParameterizedString(R.string.do_not_keep_process)

internal actual val Strings.DisableOpenGL: ParameterizedString get() =
    ParameterizedString(R.string.disable_opengl)

internal actual val Strings.DisableAGSL: ParameterizedString get() =
    ParameterizedString(R.string.disable_agsl)

internal actual val Strings.Shape: ParameterizedString get() =
    ParameterizedString(R.string.shape)

internal actual fun Strings.SizeFractionLabelAndValue(sizeFraction: Float): ParameterizedString =
    ParameterizedString(
        R.string.size_fraction_label_and_value,
        ParameterizedStringArgument(sizeFraction),
    )

internal actual fun Strings.SizeFractionValue(sizeFraction: Float): ParameterizedString =
    ParameterizedString(
        R.string.size_fraction_value,
        ParameterizedStringArgument(sizeFraction),
    )

internal actual val Strings.SizeFractionLabel: ParameterizedString get() =
    ParameterizedString(R.string.size_fraction_label)

internal actual fun Strings.CornerFractionLabelAndValue(cornerFraction: Float): ParameterizedString =
    ParameterizedString(
        R.string.corner_fraction_label_and_value,
        ParameterizedStringArgument(cornerFraction),
    )

internal actual fun Strings.CornerFractionValue(cornerFraction: Float): ParameterizedString =
    ParameterizedString(
        R.string.corner_fraction_value,
        ParameterizedStringArgument(cornerFraction),
    )

internal actual val Strings.CornerFractionLabel: ParameterizedString get() =
    ParameterizedString(R.string.corner_fraction_label)

internal actual val Strings.RoundRectangle: ParameterizedString get() =
    ParameterizedString(R.string.round_rectangle)

internal actual val Strings.DarkThemeConfig: ParameterizedString get() =
    ParameterizedString(R.string.dark_theme_config)

internal actual val Strings.FollowSystem: ParameterizedString get() =
    ParameterizedString(R.string.follow_system)

internal actual val Strings.DarkTheme: ParameterizedString get() =
    ParameterizedString(R.string.dark_theme)

internal actual val Strings.LightTheme: ParameterizedString get() =
    ParameterizedString(R.string.light_theme)

internal actual val Strings.QuickSettingsInfo: ParameterizedString get() =
    ParameterizedString(R.string.quick_settings_info)

internal actual val Strings.SeeAll: ParameterizedString get() =
    ParameterizedString(R.string.see_all)

internal actual val Strings.Back: ParameterizedString get() =
    ParameterizedString(R.string.back)

internal actual val Strings.Algorithm: ParameterizedString get() =
    ParameterizedString(R.string.algorithm)

internal actual val Strings.FeatureFlags: ParameterizedString get() =
    ParameterizedString(R.string.feature_flags)

internal actual val Strings.PatternCollections: ParameterizedString get() =
    ParameterizedString(R.string.pattern_collections)

internal actual val Strings.Visual: ParameterizedString get() =
    ParameterizedString(R.string.visual)

internal actual val Strings.ClipboardWatchingOnboardingCompleted: ParameterizedString get() =
    ParameterizedString(R.string.clipboard_watching_onboarding_completed)

internal actual val Strings.EnableClipboardWatching: ParameterizedString get() =
    ParameterizedString(R.string.enable_clipboard_watching)

internal actual val Strings.Delete: ParameterizedString get() =
    ParameterizedString(R.string.delete)

internal actual val Strings.SynchronizePatternCollectionsOnMeteredNetwork: ParameterizedString get() =
    ParameterizedString(R.string.synchronize_pattern_collections_on_metered_network)

internal actual val Strings.PatternCollectionsSynchronizationPeriod: ParameterizedString get() =
    ParameterizedString(R.string.pattern_collection_synchronization_period)

internal actual fun Strings.PatternCollectionsSynchronizationPeriodLabelAndValue(period: Double): ParameterizedString =
    ParameterizedString(
        R.string.pattern_collection_synchronization_period_label_and_value,
        ParameterizedStringArgument(period),
    )

internal actual fun Strings.PatternCollectionsSynchronizationPeriodValue(period: Double): ParameterizedString =
    ParameterizedString(
        R.string.pattern_collection_synchronization_period_value,
        ParameterizedStringArgument(period),
    )

internal actual val Strings.PatternCollectionsSynchronizationPeriodSuffix: ParameterizedString get() =
    ParameterizedString(R.string.pattern_collection_synchronization_period_suffix)

internal actual val Strings.AddPatternCollection: ParameterizedString get() =
    ParameterizedString(R.string.add_pattern_collection)

internal actual val Strings.LastSuccessfulSync: ParameterizedString get() =
    ParameterizedString(R.string.last_successful_sync)

internal actual val Strings.LastUnsuccessfulSync: ParameterizedString get() =
    ParameterizedString(R.string.last_unsuccessful_sync)

internal actual val Strings.DayUnit: ParameterizedString get() =
    ParameterizedString(R.string.day_unit)

internal actual val Strings.HourUnit: ParameterizedString get() =
    ParameterizedString(R.string.hour_unit)

internal actual val Strings.MinuteUnit: ParameterizedString get() =
    ParameterizedString(R.string.minute_unit)

internal actual val Strings.SecondUnit: ParameterizedString get() =
    ParameterizedString(R.string.second_unit)

internal actual val Strings.Never: ParameterizedString get() =
    ParameterizedString(R.string.never)

internal actual val Strings.Sources: ParameterizedString get() =
    ParameterizedString(R.string.sources)

internal actual val Strings.SourceUrlLabel: ParameterizedString get() =
    ParameterizedString(R.string.source_url_label)
