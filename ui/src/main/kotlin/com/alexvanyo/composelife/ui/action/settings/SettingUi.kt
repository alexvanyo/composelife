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

package com.alexvanyo.composelife.ui.action.settings

import androidx.compose.runtime.Composable
import androidx.compose.ui.Modifier
import dagger.hilt.EntryPoint
import dagger.hilt.InstallIn
import dagger.hilt.android.components.ActivityComponent

@EntryPoint
@InstallIn(ActivityComponent::class)
interface SettingUiEntryPoint :
    AlgorithmImplementationUiEntryPoint,
    DarkThemeConfigUiEntryPoint

context(SettingUiEntryPoint)
@Composable
fun SettingUi(
    setting: Setting,
    modifier: Modifier = Modifier,
) {
    when (setting) {
        Setting.AlgorithmImplementation -> AlgorithmImplementationUi(modifier = modifier)
        Setting.DarkThemeConfig -> DarkThemeConfigUi(modifier = modifier)
    }
}
