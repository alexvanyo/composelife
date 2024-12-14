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

import androidx.compose.animation.AnimatedContent
import androidx.compose.animation.AnimatedVisibility
import androidx.compose.animation.ExperimentalSharedTransitionApi
import androidx.compose.animation.SharedTransitionScope
import androidx.compose.animation.core.MutableTransitionState
import androidx.compose.foundation.ScrollState
import androidx.compose.foundation.layout.Column
import androidx.compose.foundation.layout.fillMaxWidth
import androidx.compose.foundation.layout.padding
import androidx.compose.foundation.rememberScrollState
import androidx.compose.foundation.verticalScroll
import androidx.compose.material3.Text
import androidx.compose.material3.TextButton
import androidx.compose.runtime.Composable
import androidx.compose.runtime.DisposableEffect
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.key
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.remember
import androidx.compose.runtime.setValue
import androidx.compose.runtime.snapshotFlow
import androidx.compose.ui.Alignment
import androidx.compose.ui.Modifier
import androidx.compose.ui.text.style.TextAlign
import androidx.compose.ui.unit.dp
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResource
import com.alexvanyo.composelife.preferences.QuickAccessSetting
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.di.LoadedComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.ordinal
import com.alexvanyo.composelife.ui.settings.resources.QuickSettingsInfo
import com.alexvanyo.composelife.ui.settings.resources.SeeAll
import com.alexvanyo.composelife.ui.settings.resources.Strings
import com.alexvanyo.composelife.ui.util.trySharedBounds
import kotlinx.coroutines.flow.collect
import kotlinx.coroutines.flow.map
import kotlinx.coroutines.flow.onEach

interface InlineSettingsPaneInjectEntryPoint :
    ComposeLifePreferencesProvider,
    SettingUiInjectEntryPoint

interface InlineSettingsPaneLocalEntryPoint :
    LoadedComposeLifePreferencesProvider,
    SettingUiLocalEntryPoint

context(InlineSettingsPaneInjectEntryPoint, InlineSettingsPaneLocalEntryPoint)
@OptIn(ExperimentalSharedTransitionApi::class)
@Suppress("LongMethod")
@Composable
fun InlineSettingsPane(
    onSeeMoreClicked: () -> Unit,
    onOpenInSettingsClicked: (Setting) -> Unit,
    modifier: Modifier = Modifier,
    scrollState: ScrollState = rememberScrollState(initial = Int.MAX_VALUE),
) {
    Column(
        modifier = modifier
            .fillMaxWidth()
            .verticalScroll(
                state = scrollState,
                reverseScrolling = true,
            )
            .padding(vertical = 8.dp),
        horizontalAlignment = Alignment.CenterHorizontally,
    ) {
        val quickAccessSettings = preferences.quickAccessSettings

        /**
         * The list of previously known animatable quick access settings, used to smoothly animate out upon
         * removing and in upon appearing.
         *
         * These are initialized to be visible, with no appearing animation
         */
        var previouslyAnimatableQuickAccessSettings by remember {
            mutableStateOf(
                quickAccessSettings.associateWith { MutableTransitionState(true) },
            )
        }

        /**
         * The list of currently animatable quick access settings. The order of the [Map.plus] is important
         * here, to preserve any ongoing animation state.
         */
        val animatableQuickAccessSettings =
            quickAccessSettings.associateWith {
                MutableTransitionState(false).apply {
                    targetState = true
                }
            } + previouslyAnimatableQuickAccessSettings

        DisposableEffect(animatableQuickAccessSettings, quickAccessSettings) {
            animatableQuickAccessSettings.forEach { (quickAccessSetting, visibleState) ->
                // Update the target state based on whether the setting should currently be visible
                visibleState.targetState = quickAccessSetting in quickAccessSettings
            }
            onDispose {}
        }

        val animatingQuickAccessSettings = animatableQuickAccessSettings
            .keys.sortedBy(QuickAccessSetting::ordinal)

        AnimatedContent(
            targetState = quickAccessSettings.isEmpty(),
        ) { showQuickAccessInfo ->
            if (showQuickAccessInfo) {
                Text(
                    text = parameterizedStringResource(Strings.QuickSettingsInfo),
                    textAlign = TextAlign.Center,
                    modifier = Modifier.padding(horizontal = 16.dp),
                )
            } else {
                Column {
                    animatingQuickAccessSettings.forEach { quickAccessSetting ->
                        key(quickAccessSetting) {
                            AnimatedVisibility(
                                visibleState = animatableQuickAccessSettings.getValue(quickAccessSetting),
                            ) {
                                SettingUi(
                                    setting = quickAccessSetting.setting,
                                    onOpenInSettingsClicked = onOpenInSettingsClicked,
                                    modifier = Modifier
                                        .padding(horizontal = 16.dp)
                                        .trySharedBounds(
                                            key = "SettingUi-${quickAccessSetting.setting}",
                                            resizeMode = SharedTransitionScope.ResizeMode.RemeasureToBounds,
                                        ),
                                )
                            }
                        }
                    }
                }
            }
        }

        // Sync all of the known quick access settings back to `previouslyAnimatableQuickAccessSettings`,
        // removing any that have finished disappearing
        LaunchedEffect(animatableQuickAccessSettings) {
            snapshotFlow {
                animatableQuickAccessSettings.values.firstOrNull {
                    it.isIdle && !it.targetState
                }
            }
                // Intentionally ignore the setting that has animated out, we're just using it to trigger
                // updating `previouslyAnimatableQuickAccessSettings` in its entirety.
                .map {}
                .onEach {
                    previouslyAnimatableQuickAccessSettings = animatableQuickAccessSettings.filterValues {
                        // Only keep those that are visible, or are currently animating
                        !it.isIdle || it.targetState
                    }
                }
                .collect()
        }

        TextButton(
            onClick = onSeeMoreClicked,
        ) {
            Text(text = parameterizedStringResource(Strings.SeeAll))
        }
    }
}
