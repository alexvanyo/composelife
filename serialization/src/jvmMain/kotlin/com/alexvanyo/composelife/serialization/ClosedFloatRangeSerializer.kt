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

package com.alexvanyo.composelife.serialization

import androidx.compose.ui.util.packFloats
import androidx.compose.ui.util.unpackFloat1
import androidx.compose.ui.util.unpackFloat2
import kotlinx.serialization.KSerializer
import kotlinx.serialization.descriptors.PrimitiveKind
import kotlinx.serialization.descriptors.PrimitiveSerialDescriptor
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.encoding.Decoder
import kotlinx.serialization.encoding.Encoder

/**
 * A [KSerializer] for a [ClosedRange] of [Float].
 */
object ClosedFloatRangeSerializer : KSerializer<ClosedRange<Float>> {
    override val descriptor: SerialDescriptor = PrimitiveSerialDescriptor(
        "kotlin.ranges.ClosedFloatRange",
        PrimitiveKind.LONG,
    )

    override fun deserialize(decoder: Decoder): ClosedRange<Float> {
        val longValue = decoder.decodeLong()
        return unpackFloat1(longValue)..unpackFloat2(longValue)
    }

    override fun serialize(encoder: Encoder, value: ClosedRange<Float>) {
        encoder.encodeLong(packFloats(value.start, value.endInclusive))
    }
}
