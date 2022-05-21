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

package com.alexvanyo.composelife.ui.entrypoints.preferences

import androidx.compose.runtime.Composable
import androidx.compose.ui.platform.LocalInspectionMode
import androidx.hilt.navigation.compose.hiltViewModel
import androidx.lifecycle.ViewModel
import com.alexvanyo.composelife.preferences.AlgorithmType
import com.alexvanyo.composelife.preferences.ComposeLifePreferences
import com.alexvanyo.composelife.preferences.CurrentShape
import com.alexvanyo.composelife.preferences.CurrentShapeType
import com.alexvanyo.composelife.preferences.DarkThemeConfig
import com.alexvanyo.composelife.preferences.TestComposeLifePreferences
import dagger.hilt.android.lifecycle.HiltViewModel
import javax.inject.Inject

@HiltViewModel
private class ComposeLifePreferencesEntryPoint @Inject constructor(
    val composeLifePreferences: ComposeLifePreferences,
) : ViewModel()

@Composable
fun inject(
    testComposeLifePreferences: TestComposeLifePreferences = TestComposeLifePreferences.Loaded(
        algorithmChoice = AlgorithmType.NaiveAlgorithm,
        currentShapeType = CurrentShapeType.RoundRectangle,
        roundRectangleConfig = CurrentShape.RoundRectangle(
            sizeFraction = 1.0f,
            cornerFraction = 0.0f,
        ),
        darkThemeConfig = DarkThemeConfig.FollowSystem,
    ),
): ComposeLifePreferences =
    if (LocalInspectionMode.current) {
        testComposeLifePreferences
    } else {
        hiltViewModel<ComposeLifePreferencesEntryPoint>().composeLifePreferences
    }
