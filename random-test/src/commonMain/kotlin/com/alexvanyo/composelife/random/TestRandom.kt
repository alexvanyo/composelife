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

package com.alexvanyo.composelife.random

import com.alexvanyo.composelife.random.di.RandomBindings
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.ContributesBinding
import dev.zacsweers.metro.Inject
import dev.zacsweers.metro.SingleIn
import kotlin.random.Random

@SingleIn(AppScope::class)
@Inject
@ContributesBinding(AppScope::class, replaces = [RandomBindings::class])
class TestRandom : Random() {
    private var randomDelegate: Random = Random

    override fun nextBits(bitCount: Int): Int = randomDelegate.nextBits(bitCount)

    fun setSeed(seed: Int) {
        randomDelegate = Random(seed)
    }
}
