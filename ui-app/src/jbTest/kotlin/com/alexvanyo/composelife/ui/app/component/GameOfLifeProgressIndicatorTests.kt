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

package com.alexvanyo.composelife.ui.app.component

import androidx.compose.ui.semantics.ProgressBarRangeInfo
import androidx.compose.ui.semantics.SemanticsProperties
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.SemanticsMatcher
import androidx.compose.ui.test.assert
import androidx.compose.ui.test.hasProgressBarRangeInfo
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferences
import com.alexvanyo.composelife.test.BaseUiInjectTest2
import com.alexvanyo.composelife.test.runUiTest
import com.alexvanyo.composelife.ui.app.TestComposeLifeApplicationComponent
import com.alexvanyo.composelife.ui.app.TestComposeLifeUiComponent
import com.alexvanyo.composelife.ui.app.createComponent
import kotlin.test.Test

@OptIn(ExperimentalTestApi::class)
class GameOfLifeProgressIndicatorTests : BaseUiInjectTest2<TestComposeLifeApplicationComponent, TestComposeLifeUiComponent>(
    TestComposeLifeApplicationComponent::createComponent,
    TestComposeLifeUiComponent::createComponent,
) {
    private val gameOfLifeProgressIndicatorLocalEntryPoint = object : GameOfLifeProgressIndicatorLocalEntryPoint {
        override val preferences = LoadedComposeLifePreferences.Defaults
    }

    @Test
    fun progress_indicator_is_displayed_correctly() = runUiTest {
        val gameOfLifeProgressIndicatorInjectEntryPoint: GameOfLifeProgressIndicatorInjectEntryPoint =
            uiComponent.entryPoint

        setContent {
            with(gameOfLifeProgressIndicatorInjectEntryPoint) {
                with(gameOfLifeProgressIndicatorLocalEntryPoint) {
                    GameOfLifeProgressIndicator()
                }
            }
        }

        onNode(SemanticsMatcher.keyIsDefined(SemanticsProperties.ProgressBarRangeInfo))
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo.Indeterminate))
    }
}
