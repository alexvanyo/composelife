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

package com.alexvanyo.composelife.ui.app

import com.alexvanyo.composelife.algorithm.GameOfLifeAlgorithm
import com.alexvanyo.composelife.dispatchers.CellTickerTestDispatcher
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.dispatchers.GeneralTestDispatcher
import com.alexvanyo.composelife.model.CellStateParser
import com.alexvanyo.composelife.preferences.ComposeLifePreferences
import com.alexvanyo.composelife.updatable.Updatable
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.ContributesTo
import kotlinx.coroutines.test.TestDispatcher

@ContributesTo(AppScope::class)
interface TestComposeLifeApplicationEntryPoint {
    val updatables: Set<Updatable>
    val dispatchers: ComposeLifeDispatchers
    val gameOfLifeAlgorithm: GameOfLifeAlgorithm
    val composeLifePreferences: ComposeLifePreferences
    val cellStateParser: CellStateParser
    @GeneralTestDispatcher val generalTestDispatcher: TestDispatcher
    @CellTickerTestDispatcher val cellTickerTestDispatcher: TestDispatcher
}
