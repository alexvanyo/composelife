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
import androidx.compose.ui.test.SemanticsMatcher
import androidx.compose.ui.test.assert
import androidx.compose.ui.test.hasProgressBarRangeInfo
import com.alexvanyo.composelife.preferences.LoadedComposeLifePreferences
import com.alexvanyo.composelife.test.BaseUiHiltTest
import com.alexvanyo.composelife.test.TestActivity
import dagger.hilt.EntryPoints
import dagger.hilt.android.testing.HiltAndroidTest
import kotlinx.coroutines.ExperimentalCoroutinesApi
import leakcanary.SkipLeakDetection
import kotlin.test.BeforeTest
import kotlin.test.Test

@OptIn(ExperimentalCoroutinesApi::class)
@HiltAndroidTest
class GameOfLifeProgressIndicatorTests : BaseUiHiltTest<TestActivity>(TestActivity::class.java) {

    private lateinit var gameOfLifeProgressIndicatorHiltEntryPoint: GameOfLifeProgressIndicatorHiltEntryPoint

    private val gameOfLifeProgressIndicatorLocalEntryPoint = object : GameOfLifeProgressIndicatorLocalEntryPoint {
        override val preferences = LoadedComposeLifePreferences.Defaults
    }

    @BeforeTest
    fun setup() {
        gameOfLifeProgressIndicatorHiltEntryPoint =
            EntryPoints.get(composeTestRule.activity, GameOfLifeProgressIndicatorHiltEntryPoint::class.java)
    }

    @SkipLeakDetection("recomposer", "Outer")
    @Test
    fun progress_indicator_is_displayed_correctly() = runAppTest {
        composeTestRule.setContent {
            with(gameOfLifeProgressIndicatorHiltEntryPoint) {
                with(gameOfLifeProgressIndicatorLocalEntryPoint) {
                    GameOfLifeProgressIndicator()
                }
            }
        }

        composeTestRule
            .onNode(SemanticsMatcher.keyIsDefined(SemanticsProperties.ProgressBarRangeInfo))
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo.Indeterminate))
    }
}
