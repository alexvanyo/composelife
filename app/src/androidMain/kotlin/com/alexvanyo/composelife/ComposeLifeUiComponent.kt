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

package com.alexvanyo.composelife

import android.app.Activity
import coil3.ImageLoader
import com.alexvanyo.composelife.algorithm.GameOfLifeAlgorithm
import com.alexvanyo.composelife.data.CellStateRepository
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.model.CellStateParser
import com.alexvanyo.composelife.preferences.ComposeLifePreferences
import com.alexvanyo.composelife.scopes.UiComponent
import com.alexvanyo.composelife.scopes.UiScope
import kotlinx.datetime.Clock
import me.tatarka.inject.annotations.Inject
import software.amazon.lastmile.kotlin.inject.anvil.AppScope
import software.amazon.lastmile.kotlin.inject.anvil.ContributesSubcomponent
import software.amazon.lastmile.kotlin.inject.anvil.SingleIn
import kotlin.random.Random

@ContributesSubcomponent(UiScope::class)
@SingleIn(UiScope::class)
interface ComposeLifeUiComponent : UiComponent<ComposeLifeUiEntryPoint> {
    override val entryPoint: ComposeLifeUiEntryPoint

    @ContributesSubcomponent.Factory(AppScope::class)
    interface Factory {
        fun createComponent(activity: Activity): ComposeLifeUiComponent
    }

    companion object
}

@Suppress("LongParameterList")
@SingleIn(UiScope::class)
@Inject
class ComposeLifeUiEntryPoint(
    override val gameOfLifeAlgorithm: GameOfLifeAlgorithm,
    override val composeLifePreferences: ComposeLifePreferences,
    override val cellStateRepository: CellStateRepository,
    override val clock: Clock,
    override val dispatchers: ComposeLifeDispatchers,
    override val random: Random,
    override val imageLoader: ImageLoader,
    override val cellStateParser: CellStateParser,
) : MainActivityInjectEntryPoint
