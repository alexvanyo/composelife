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

import kotlinx.serialization.KSerializer
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.encoding.Decoder
import kotlinx.serialization.encoding.Encoder
import kotlinx.serialization.serializer

/**
 * Returns a surrogating [KSerializer] of type [T] that converts to and from a surrogate of type [S], which is
 * serialized with the given [surrogateSerializer].
 */
inline fun <reified T, reified S> SurrogatingSerializer(
    noinline convertToSurrogate: (T) -> S,
    noinline convertFromSurrogate: (S) -> T,
    surrogateSerializer: KSerializer<S> = serializer(),
): KSerializer<T> =
    object : KSerializer<T> {
        override val descriptor = SerialDescriptor(
            serialName = requireNotNull(T::class.qualifiedName),
            original = surrogateSerializer.descriptor,
        )
        override fun deserialize(decoder: Decoder): T =
            convertFromSurrogate(surrogateSerializer.deserialize(decoder))

        override fun serialize(encoder: Encoder, value: T) =
            surrogateSerializer.serialize(encoder, convertToSurrogate(value))
    }
