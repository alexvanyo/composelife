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

package com.alexvanyo.composelife.ui.util

import androidx.compose.runtime.Composable
import androidx.compose.ui.Modifier
import androidx.compose.ui.UiComposable
import androidx.compose.ui.layout.Layout
import androidx.compose.ui.layout.Measurable
import androidx.compose.ui.layout.MeasurePolicy
import androidx.compose.ui.layout.MeasureResult
import androidx.compose.ui.layout.MeasureScope
import androidx.compose.ui.layout.layoutId
import androidx.compose.ui.unit.Constraints
import com.livefront.sealedenum.SealedEnum

/**
 * A more type-safe [Layout] where all measurables are expected to have a [layoutId] of type [T].
 *
 * More specifically, [T] is from the set of [layoutIdTypes] as expressed by a [SealedEnum].
 *
 * Every possible of [T] should be represented by exactly one measurable, otherwise an exception will be thrown.
 */
@UiComposable
@Composable
inline fun <T> Layout(
    layoutIdTypes: SealedEnum<T>,
    content:
        @Composable
        @UiComposable
        () -> Unit,
    modifier: Modifier = Modifier,
    measurePolicy: SealedEnumMeasurePolicy<T>,
) {
    Layout(
        content = content,
        modifier = modifier,
    ) { measurables, constraints ->
        @Suppress("UNCHECKED_CAST")
        val measurablesMap = measurables.associateBy { it.layoutId as T }
        // Check that each type T is associate with exactly one measurable
        check(measurables.size == layoutIdTypes.values.size && measurablesMap.size == layoutIdTypes.values.size)
        with(measurePolicy) {
            measure(measurablesMap, constraints)
        }
    }
}

/**
 * A [MeasurePolicy] where the [layoutId]s are of type [T], and [measure] is passed a [Map] of measurables keyed by [T].
 */
fun interface SealedEnumMeasurePolicy<T> {

    fun MeasureScope.measure(
        measurables: Map<T, Measurable>,
        constraints: Constraints,
    ): MeasureResult
}
