/*
 * Copyright 2025 The Android Open Source Project
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

package com.alexvanyo.composelife.ui.app.component

import androidx.compose.runtime.Immutable
import com.alexvanyo.composelife.algorithm.GameOfLifeAlgorithm
import com.alexvanyo.composelife.dispatchers.ComposeLifeDispatchers
import com.alexvanyo.composelife.ui.cells.ImmutableCellWindowCtxClass
import dev.zacsweers.metro.Inject
import kotlin.random.Random
import kotlin.time.Clock

@Immutable
@Inject
class GameOfLifeProgressIndicatorCtx(
    internal val immutableCellWindowCtx: ImmutableCellWindowCtxClass,
    internal val random: Random,
    internal val clock: Clock,
    internal val gameOfLifeAlgorithm: GameOfLifeAlgorithm,
    internal val dispatchers: ComposeLifeDispatchers,
) {
    companion object
}
