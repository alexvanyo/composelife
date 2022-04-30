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

package com.alexvanyo.composelife.ui.entrypoints.algorithm

import androidx.compose.runtime.Composable
import androidx.compose.ui.platform.LocalInspectionMode
import androidx.hilt.navigation.compose.hiltViewModel
import androidx.lifecycle.ViewModel
import com.alexvanyo.composelife.algorithm.GameOfLifeAlgorithm
import com.alexvanyo.composelife.algorithm.NaiveGameOfLifeAlgorithm
import dagger.hilt.android.lifecycle.HiltViewModel
import javax.inject.Inject
import kotlin.experimental.ExperimentalTypeInference
import com.alexvanyo.composelife.ui.entrypoints.dispatchers.inject as injectDispatchers

@HiltViewModel
private class GameOfLifeAlgorithmEntryPoint @Inject constructor(
    val gameOfLifeAlgorithm: GameOfLifeAlgorithm,
) : ViewModel()

@OptIn(ExperimentalTypeInference::class)
@OverloadResolutionByLambdaReturnType
@Composable
fun inject(
    previewGameOfLifeAlgorithm: GameOfLifeAlgorithm = NaiveGameOfLifeAlgorithm(injectDispatchers()),
): GameOfLifeAlgorithm =
    if (LocalInspectionMode.current) {
        previewGameOfLifeAlgorithm
    } else {
        hiltViewModel<GameOfLifeAlgorithmEntryPoint>().gameOfLifeAlgorithm
    }
