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

package com.alexvanyo.composelife.geometry

import androidx.benchmark.junit4.BenchmarkRule
import androidx.benchmark.junit4.measureRepeated
import androidx.test.ext.junit.runners.AndroidJUnit4
import org.junit.Rule
import org.junit.runner.RunWith
import kotlin.random.Random
import kotlin.test.Test
import kotlin.test.assertNotEquals

@RunWith(AndroidJUnit4::class)
class LineSegmentBenchmark {

    @get:Rule
    val benchmarkRule = BenchmarkRule()

    private val singleCellStart = Offset(2.1f, 3.4f)
    private val singleCellEnd = Offset(2.8f, 3.9f)

    private val adjacentStart = Offset(1.2f, 2.5f)
    private val adjacentEnd = Offset(2.8f, 3.5f)

    private val moderateStart = Offset(0.0f, 0.0f)
    private val moderateEnd = Offset(10.5f, 7.3f)

    private val longStart = Offset(-50.0f, -50.0f)
    private val longEnd = Offset(50.0f, 50.0f)

    private val multiPointPath = listOf(
        Offset(0f, 0f),
        Offset(12.3f, 4.5f),
        Offset(15.1f, 18.2f),
        Offset(8.4f, 25.0f),
        Offset(2.1f, 19.8f),
        Offset(-5.0f, 10.2f),
        Offset(-2.3f, 1.1f),
    )

    private val randomSegments = run {
        val random = Random(42)
        List(1000) {
            Offset(
                random.nextFloat() * 200f - 100f,
                random.nextFloat() * 200f - 100f,
            ) to Offset(
                random.nextFloat() * 200f - 100f,
                random.nextFloat() * 200f - 100f,
            )
        }
    }

    @Test
    fun benchmark_single_cell_segment() {
        benchmarkRule.measureRepeated {
            val cells = cellIntersections(singleCellStart, singleCellEnd)
            assertNotEquals(0, cells.size)
        }
    }

    @Test
    fun benchmark_adjacent_cells_segment() {
        benchmarkRule.measureRepeated {
            val cells = cellIntersections(adjacentStart, adjacentEnd)
            assertNotEquals(0, cells.size)
        }
    }

    @Test
    fun benchmark_moderate_segment() {
        benchmarkRule.measureRepeated {
            val cells = cellIntersections(moderateStart, moderateEnd)
            assertNotEquals(0, cells.size)
        }
    }

    @Test
    fun benchmark_long_segment() {
        benchmarkRule.measureRepeated {
            val cells = cellIntersections(longStart, longEnd)
            assertNotEquals(0, cells.size)
        }
    }

    @Test
    fun benchmark_multi_point_path() {
        benchmarkRule.measureRepeated {
            val cells = cellIntersections(multiPointPath)
            assertNotEquals(0, cells.size)
        }
    }

    @Test
    fun benchmark_random_batch() {
        val segments = randomSegments
        benchmarkRule.measureRepeated {
            var count = 0
            for (i in segments.indices) {
                val (start, end) = segments[i]
                count += cellIntersections(start, end).size
            }
            assertNotEquals(0, count)
        }
    }
}
