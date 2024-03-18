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

package com.alexvanyo.composelife.preferences

import com.alexvanyo.composelife.preferences.proto.RoundRectangleProto

sealed interface CurrentShape {
    val type: CurrentShapeType

    data class RoundRectangle(
        val sizeFraction: Float,
        val cornerFraction: Float,
    ) : CurrentShape {
        override val type: CurrentShapeType = CurrentShapeType.RoundRectangle
    }
}

internal fun RoundRectangleProto?.toResolved(): CurrentShape.RoundRectangle =
    if (this == null) {
        CurrentShape.RoundRectangle(
            sizeFraction = 1f,
            cornerFraction = 0f,
        )
    } else {
        CurrentShape.RoundRectangle(
            sizeFraction = size_fraction,
            cornerFraction = corner_fraction,
        )
    }

internal fun CurrentShape.RoundRectangle.toProto(): RoundRectangleProto =
    RoundRectangleProto(
        size_fraction = sizeFraction,
        corner_fraction = cornerFraction,
    )
