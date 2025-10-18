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

package com.alexvanyo.composelife.ui.util

import androidx.compose.animation.core.Easing

/**
 * Returns a piecewise [Easing] formed from other easings.
 *
 * The first [easing] will be applied from 0f until the fraction in the first entry of [easings].
 * The [Easing] in that first pair will be applied until the fraction in the second entry of [easings], and so on,
 * until the [Easing] in the last entry will apply until 1f.
 *
 * Note that intermediate [Easing]s can violate the normal rule that each [Easing] must map 0f to 0f and 1f to 1f,
 * if the overall [Easing] matches that requirement.
 */
fun Easing(
    easing: Easing,
    vararg easings: Pair<Float, Easing>,
): Easing {
    require(easings.sortedBy { it.first } == easings.toList()) { "easings were not sorted by keyframe!" }
    val allEasings = buildMap {
        put(0f, easing)
        putAll(easings)
    }
    require(allEasings.size == easings.size + 1)
    val keyList = allEasings.keys.toList()
    val easingsList = allEasings.values.toList()
    return Easing {
        val piecewiseStartIndex = keyList.floorBinarySearch(it)
        val piecewiseStart = keyList[piecewiseStartIndex]
        val piecewiseEasing = easingsList[piecewiseStartIndex]
        val piecewiseEnd = keyList.getOrElse(piecewiseStartIndex + 1) { 1f }
        piecewiseEasing.transform((it - piecewiseStart) / (piecewiseEnd - piecewiseStart))
    }
}

private fun <T : Comparable<T>> List<T>.floorBinarySearch(value: T): Int {
    var low = 0
    var high = size
    if (this[low] > value) return -1
    while (low + 1 < high) {
        val mid = (low + high) / 2
        if (this[mid] <= value) {
            low = mid
        } else {
            high = mid
        }
    }
    return low
}
