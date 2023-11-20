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

import androidx.compose.ui.geometry.Rect
import kotlinx.serialization.ExperimentalSerializationApi
import kotlinx.serialization.KSerializer
import kotlinx.serialization.builtins.FloatArraySerializer
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.encoding.Decoder
import kotlinx.serialization.encoding.Encoder

/**
 * A [KSerializer] for a [Rect].
 */
object RectSerializer : KSerializer<Rect> {
    private val delegateSerializer = FloatArraySerializer()

    @OptIn(ExperimentalSerializationApi::class)
    override val descriptor: SerialDescriptor = SerialDescriptor(
        "androidx.compose.ui.geometry.Rect",
        delegateSerializer.descriptor,
    )

    override fun deserialize(decoder: Decoder): Rect {
        val floatArray = delegateSerializer.deserialize(decoder)
        return Rect(
            left = floatArray[0],
            top = floatArray[1],
            right = floatArray[2],
            bottom = floatArray[3],
        )
    }

    override fun serialize(encoder: Encoder, value: Rect) {
        delegateSerializer.serialize(
            encoder,
            floatArrayOf(
                value.left,
                value.top,
                value.right,
                value.bottom,
            ),
        )
    }
}
