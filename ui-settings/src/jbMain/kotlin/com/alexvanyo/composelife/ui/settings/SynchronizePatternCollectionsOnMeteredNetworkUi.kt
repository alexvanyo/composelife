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

import androidx.compose.runtime.Composable
import androidx.compose.runtime.rememberCoroutineScope
import androidx.compose.ui.Modifier
import com.alexvanyo.composelife.parameterizedstring.parameterizedStringResource
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.di.LoadedComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.setSynchronizePatternCollectionsOnMeteredNetwork
import com.alexvanyo.composelife.ui.mobile.component.LabeledSwitch
import com.alexvanyo.composelife.ui.settings.resources.SynchronizePatternCollectionsOnMeteredNetwork
import com.alexvanyo.composelife.ui.settings.resources.Strings
import kotlinx.coroutines.launch

interface SynchronizePatternCollectionsOnMeteredNetworkUiInjectEntryPoint :
    ComposeLifePreferencesProvider

interface SynchronizePatternCollectionsOnMeteredNetworkUiLocalEntryPoint :
    LoadedComposeLifePreferencesProvider

context(
    injectEntryPoint: SynchronizePatternCollectionsOnMeteredNetworkUiInjectEntryPoint,
    localEntryPoint: SynchronizePatternCollectionsOnMeteredNetworkUiLocalEntryPoint
)
@Composable
fun SynchronizePatternCollectionsOnMeteredNetworkUi(
    modifier: Modifier = Modifier,
) {
    SynchronizePatternCollectionsOnMeteredNetworkUi(
        synchronizePatternCollectionsOnMeteredNetwork =
            localEntryPoint.preferences.synchronizePatternCollectionsOnMeteredNetwork,
        setSynchronizePatternCollectionsOnMeteredNetwork =
            injectEntryPoint.composeLifePreferences::setSynchronizePatternCollectionsOnMeteredNetwork,
        modifier = modifier,
    )
}

@Composable
fun SynchronizePatternCollectionsOnMeteredNetworkUi(
    synchronizePatternCollectionsOnMeteredNetwork: Boolean,
    setSynchronizePatternCollectionsOnMeteredNetwork: suspend (Boolean) -> Unit,
    modifier: Modifier = Modifier,
) {
    val coroutineScope = rememberCoroutineScope()
    LabeledSwitch(
        label = parameterizedStringResource(Strings.SynchronizePatternCollectionsOnMeteredNetwork),
        checked = synchronizePatternCollectionsOnMeteredNetwork,
        onCheckedChange = { enabled ->
            coroutineScope.launch {
                setSynchronizePatternCollectionsOnMeteredNetwork(enabled)
            }
        },
        modifier = modifier,
    )
}
