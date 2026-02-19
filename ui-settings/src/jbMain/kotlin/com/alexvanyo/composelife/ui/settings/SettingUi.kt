/*
 * Copyright 2022 The Android Open Source Project
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
@file:Suppress("MatchingDeclarationName")

package com.alexvanyo.composelife.ui.settings

import androidx.compose.foundation.layout.Column
import androidx.compose.material3.MaterialTheme
import androidx.compose.material3.Surface
import androidx.compose.runtime.Composable
import androidx.compose.runtime.Immutable
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.ui.Modifier
import androidx.compose.ui.platform.testTag
import com.alexvanyo.composelife.preferences.ComposeLifePreferences
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferencesHolder
import com.alexvanyo.composelife.preferences.QuickAccessSetting
import com.alexvanyo.composelife.preferences.addQuickAccessSetting
import com.alexvanyo.composelife.preferences.removeQuickAccessSetting
import com.alexvanyo.composelife.ui.mobile.component.LocalBackgroundColor
import dev.zacsweers.metro.Inject
import kotlinx.coroutines.launch

@Suppress("LongParameterList")
@Immutable
@Inject
class IndividualSettingCtx(
    val algorithmImplementationUiCtx: AlgorithmImplementationUiCtx,
    val cellStatePreviewUiCtx: CellStatePreviewUiCtx,
    val darkThemeConfigUiCtx: DarkThemeConfigUiCtx,
    val cellShapeConfigUiCtx: CellShapeConfigUiCtx,
    val synchronizePatternCollectionsOnMeteredNetworkUiCtx:
    SynchronizePatternCollectionsOnMeteredNetworkUiCtx,
    val patternCollectionsSynchronizationPeriodUiCtx:
    PatternCollectionsSynchronizationPeriodUiCtx,
    val patternCollectionsUiCtx: PatternCollectionsUiCtx,
    val disableAGSLUiCtx: DisableAGSLUiCtx,
    val disableOpenGLUiCtx: DisableOpenGLUiCtx,
    val doNotKeepProcessUiCtx: DoNotKeepProcessUiCtx,
    val enableClipboardWatchingUiCtx: EnableClipboardWatchingUiCtx,
    val clipboardWatchingOnboardingCompletedUiCtx: ClipboardWatchingOnboardingCompletedUiCtx,
    val enableWindowShapeClippingUiCtx: EnableWindowShapeClippingUiCtx,
    val cellStatePruningPeriodUiCtx: CellStatePruningPeriodUiCtx,
)

// region templated-ctx
@Immutable
@Inject
@Suppress("LongParameterList")
class SettingUiCtx(
    private val preferencesHolder: LoadedComposeLifePreferencesHolder,
    private val composeLifePreferences: ComposeLifePreferences,
    private val individualSettingCtx: IndividualSettingCtx,
) {
    @Suppress("ComposableNaming", "LongParameterList")
    @Deprecated(
        "Ctx should not be invoked directly, instead use the top-level function",
        replaceWith = ReplaceWith(
            "SettingUi(setting, modifier, onOpenInSettingsClicked)",
        ),
    )
    @Composable
    operator fun invoke(
        setting: Setting,
        modifier: Modifier = Modifier,
        onOpenInSettingsClicked: ((Setting) -> Unit)? = null,
    ) = lambda(
        preferencesHolder,
        composeLifePreferences,
        individualSettingCtx,
        setting,
        modifier,
        onOpenInSettingsClicked,
    )

    companion object {
        private val lambda:
            @Composable context(
                LoadedComposeLifePreferencesHolder,
                ComposeLifePreferences,
                IndividualSettingCtx,
            ) (
                setting: Setting,
                modifier: Modifier,
                onOpenInSettingsClicked: ((Setting) -> Unit)?,
            ) -> Unit =
            { setting, modifier, onOpenInSettingsClicked ->
                SettingUi(setting, modifier, onOpenInSettingsClicked)
            }
    }
}

context(ctx: SettingUiCtx)
@Suppress("DEPRECATION")
@Composable
fun SettingUi(
    setting: Setting,
    modifier: Modifier = Modifier,
    onOpenInSettingsClicked: ((Setting) -> Unit)? = null,
) = ctx(setting, modifier, onOpenInSettingsClicked)
// endregion templated-ctx

/**
 * Displays the setting UI for the given [setting].
 *
 * If [onOpenInSettingsClicked] is not null, then a button will be displayed to open the given
 * setting that will invoke [onOpenInSettingsClicked].
 */
context(
    preferencesHolder: LoadedComposeLifePreferencesHolder,
composeLifePreferences: ComposeLifePreferences,
individualSettingCtx: IndividualSettingCtx,
)
@Suppress("CyclomaticComplexMethod", "LongMethod")
@Composable
private fun SettingUi(
    setting: Setting,
    modifier: Modifier = Modifier,
    onOpenInSettingsClicked: ((Setting) -> Unit)? = null,
) {
    Surface(
        color = LocalBackgroundColor.current ?: MaterialTheme.colorScheme.surface,
        modifier = modifier.testTag("SettingUi:${setting._name}"),
    ) {
        Column {
            val quickAccessSetting = setting.quickAccessSetting
            if (quickAccessSetting != null) {
                val coroutineScope = rememberCoroutineScope()
                QuickAccessSettingHeader(
                    isFavorite = quickAccessSetting in preferencesHolder.preferences.quickAccessSettings,
                    setIsFavorite = { isFavorite ->
                        coroutineScope.launch {
                            if (isFavorite) {
                                composeLifePreferences.addQuickAccessSetting(quickAccessSetting)
                            } else {
                                composeLifePreferences.removeQuickAccessSetting(quickAccessSetting)
                            }
                        }
                    },
                    onOpenInSettingsClicked = onOpenInSettingsClicked?.let { { it(setting) } },
                )
            }

            when (setting) {
                Setting.AlgorithmImplementation -> with(individualSettingCtx.algorithmImplementationUiCtx) {
                    AlgorithmImplementationUi()
                }
                Setting.CellStatePreview -> with(individualSettingCtx.cellStatePreviewUiCtx) {
                    CellStatePreviewUi()
                }
                Setting.DarkThemeConfig -> with(individualSettingCtx.darkThemeConfigUiCtx) {
                    DarkThemeConfigUi()
                }
                Setting.CellShapeConfig -> with(individualSettingCtx.cellShapeConfigUiCtx) {
                    CellShapeConfigUi()
                }
                Setting.SynchronizePatternCollectionsOnMeteredNetwork -> with(
                    individualSettingCtx.synchronizePatternCollectionsOnMeteredNetworkUiCtx,
                ) {
                    SynchronizePatternCollectionsOnMeteredNetworkUi()
                }
                Setting.PatternCollectionsSynchronizationPeriod -> with(
                    individualSettingCtx.patternCollectionsSynchronizationPeriodUiCtx,
                ) {
                    PatternCollectionsSynchronizationPeriodUi()
                }
                Setting.PatternCollectionSources -> with(individualSettingCtx.patternCollectionsUiCtx) {
                    PatternCollectionsUi()
                }
                Setting.DisableAGSL -> with(individualSettingCtx.disableAGSLUiCtx) {
                    DisableAGSLUi()
                }
                Setting.DisableOpenGL -> with(individualSettingCtx.disableOpenGLUiCtx) {
                    DisableOpenGLUi()
                }
                Setting.DoNotKeepProcess -> with(individualSettingCtx.doNotKeepProcessUiCtx) {
                    DoNotKeepProcessUi()
                }
                Setting.EnableClipboardWatching -> with(individualSettingCtx.enableClipboardWatchingUiCtx) {
                    EnableClipboardWatchingUi()
                }
                Setting.ClipboardWatchingOnboardingCompleted -> with(
                    individualSettingCtx.clipboardWatchingOnboardingCompletedUiCtx,
                ) {
                    ClipboardWatchingOnboardingCompletedUi()
                }
                Setting.EnableWindowShapeClipping -> with(individualSettingCtx.enableWindowShapeClippingUiCtx) {
                    EnableWindowShapeClippingUi()
                }
                Setting.CellStatePruningPeriod -> with(individualSettingCtx.cellStatePruningPeriodUiCtx) {
                    CellStatePruningPeriodUi()
                }
            }
        }
    }
}

val QuickAccessSetting.setting: Setting
    get() =
        when (this) {
            QuickAccessSetting.AlgorithmImplementation -> Setting.AlgorithmImplementation
            QuickAccessSetting.CellShapeConfig -> Setting.CellShapeConfig
            QuickAccessSetting.SynchronizePatternCollectionsOnMeteredNetwork ->
                Setting.SynchronizePatternCollectionsOnMeteredNetwork
            QuickAccessSetting.PatternCollectionsSynchronizationPeriod ->
                Setting.PatternCollectionsSynchronizationPeriod
            QuickAccessSetting.DarkThemeConfig -> Setting.DarkThemeConfig
            QuickAccessSetting.DisableAGSL -> Setting.DisableAGSL
            QuickAccessSetting.DisableOpenGL -> Setting.DisableOpenGL
            QuickAccessSetting.DoNotKeepProcess -> Setting.DoNotKeepProcess
            QuickAccessSetting.EnableClipboardWatching -> Setting.EnableClipboardWatching
            QuickAccessSetting.ClipboardWatchingOnboardingCompleted -> Setting.ClipboardWatchingOnboardingCompleted
            QuickAccessSetting.EnableWindowShapeClipping -> Setting.EnableWindowShapeClipping
            QuickAccessSetting.CellStatePruningPeriod -> Setting.CellStatePruningPeriod
        }
