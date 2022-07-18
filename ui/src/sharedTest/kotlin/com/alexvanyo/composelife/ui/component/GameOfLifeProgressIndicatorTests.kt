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

package com.alexvanyo.composelife.ui.component

import androidx.compose.ui.semantics.ProgressBarRangeInfo
import androidx.compose.ui.semantics.SemanticsProperties
import androidx.compose.ui.test.SemanticsMatcher
import androidx.compose.ui.test.assert
import androidx.compose.ui.test.hasProgressBarRangeInfo
import com.alexvanyo.composelife.test.BaseHiltTest
import com.alexvanyo.composelife.test.TestActivity
import dagger.hilt.EntryPoints
import dagger.hilt.android.testing.HiltAndroidTest
import kotlinx.coroutines.ExperimentalCoroutinesApi
import org.junit.Before
import org.junit.Test

@OptIn(ExperimentalCoroutinesApi::class)
@HiltAndroidTest
class GameOfLifeProgressIndicatorTests : BaseHiltTest<TestActivity>(TestActivity::class.java) {

    lateinit var gameOfLifeProgressIndicatorEntryPoint: GameOfLifeProgressIndicatorEntryPoint

    @Before
    fun setup() {
        gameOfLifeProgressIndicatorEntryPoint =
            EntryPoints.get(composeTestRule.activity, GameOfLifeProgressIndicatorEntryPoint::class.java)
    }

    @Test
    fun progress_indicator_is_displayed_correctly_when_shape_is_loading() = runAppTest(
        preferencesInitializer = {},
    ) {
        composeTestRule.setContent {
            with(gameOfLifeProgressIndicatorEntryPoint) {
                GameOfLifeProgressIndicator()
            }
        }

        composeTestRule
            .onNode(SemanticsMatcher.keyIsDefined(SemanticsProperties.ProgressBarRangeInfo))
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo.Indeterminate))
    }

    @Test
    fun progress_indicator_is_displayed_correctly_when_shape_is_not_loading() = runAppTest {
        composeTestRule.setContent {
            with(gameOfLifeProgressIndicatorEntryPoint) {
                GameOfLifeProgressIndicator()
            }
        }

        composeTestRule
            .onNode(SemanticsMatcher.keyIsDefined(SemanticsProperties.ProgressBarRangeInfo))
            .assert(hasProgressBarRangeInfo(ProgressBarRangeInfo.Indeterminate))
    }
}
