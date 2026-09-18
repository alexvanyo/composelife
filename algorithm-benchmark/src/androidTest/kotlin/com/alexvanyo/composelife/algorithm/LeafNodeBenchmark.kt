/*
 * Copyright 2026 The Android Open Source Project
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

package com.alexvanyo.composelife.algorithm

import androidx.benchmark.junit4.BenchmarkRule
import androidx.benchmark.junit4.measureRepeated
import androidx.test.ext.junit.runners.AndroidJUnit4
import org.junit.Rule
import org.junit.runner.RunWith
import kotlin.random.Random
import kotlin.test.Test
import kotlin.test.assertNotEquals

@RunWith(AndroidJUnit4::class)
class LeafNodeBenchmark {

    @get:Rule
    val benchmarkRule = BenchmarkRule()

    private val emptyLeaf = 0L
    private val blockLeaf = (1L shl 0x0F) or (1L shl 0x1A) or (1L shl 0x25) or (1L shl 0x30)
    private val blinkerLeaf = (1L shl 0x0E) or (1L shl 0x0F) or (1L shl 0x1A)

    private val diverseLeaves = run {
        val random = Random(42)
        LongArray(64) {
            when (it % 4) {
                0 -> 0L
                1 -> blockLeaf
                2 -> blinkerLeaf
                else -> random.nextLong()
            }
        }
    }

    @Test
    fun benchmark_leaf_empty() {
        benchmarkRule.measureRepeated {
            emptyLeaf.computeLeafNextGeneration()
        }
    }

    @Test
    fun benchmark_leaf_block() {
        benchmarkRule.measureRepeated {
            blockLeaf.computeLeafNextGeneration()
        }
    }

    @Test
    fun benchmark_leaf_blinker() {
        benchmarkRule.measureRepeated {
            blinkerLeaf.computeLeafNextGeneration()
        }
    }

    @Test
    fun benchmark_leaf_batch() {
        val leaves = diverseLeaves
        benchmarkRule.measureRepeated {
            var sum = 0
            for (i in 0 until leaves.size) {
                sum = sum xor leaves[i].computeLeafNextGeneration()
            }
            assertNotEquals(-1, sum)
        }
    }
}
