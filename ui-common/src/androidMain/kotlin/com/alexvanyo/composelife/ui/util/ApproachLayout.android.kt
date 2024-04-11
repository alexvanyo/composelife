/*
 * Copyright 2024 The Android Open Source Project
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

import androidx.compose.ui.Modifier
import androidx.compose.ui.layout.LayoutCoordinates
import androidx.compose.ui.layout.Measurable
import androidx.compose.ui.layout.MeasureResult
import androidx.compose.ui.layout.Placeable
import androidx.compose.ui.layout.approachLayout
import androidx.compose.ui.unit.Constraints
import androidx.compose.ui.unit.IntSize

actual fun Modifier.approachLayout(
    isMeasurementApproachInProgress: (lookaheadSize: IntSize) -> Boolean,
    isPlacementApproachInProgress: Placeable.PlacementScope.(
        lookaheadCoordinates: LayoutCoordinates,
    ) -> Boolean,
    approachMeasure: ApproachMeasureScope.(
        measurable: Measurable,
        constraints: Constraints,
    ) -> MeasureResult,
): Modifier = approachLayout(
    isMeasurementApproachInProgress = isMeasurementApproachInProgress,
    isPlacementApproachInProgress = isPlacementApproachInProgress,
    approachMeasure = approachMeasure,
)

actual typealias ApproachMeasureScope = androidx.compose.ui.layout.ApproachMeasureScope

actual fun ApproachMeasureScope.lookaheadSize(): IntSize = lookaheadSize
