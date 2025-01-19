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

package com.alexvanyo.composelife.imageloader.di

import coil3.ComponentRegistry
import coil3.key.Keyer
import software.amazon.lastmile.kotlin.inject.anvil.AppScope
import software.amazon.lastmile.kotlin.inject.anvil.SingleIn
import kotlin.reflect.KClass

interface ImageLoaderKeyerComponent {
    @get:SingleIn(AppScope::class)
    val keyers: Set<KeyerWithType<out Any>>
}

class KeyerWithType<T : Any>(
    val type: KClass<T>,
    val keyer: Keyer<T>,
)

fun <T : Any> KeyerWithType<T>.addTo(componentRegistryBuilder: ComponentRegistry.Builder) {
    componentRegistryBuilder.add(keyer, type)
}

inline fun <reified T : Any> Keyer<T>.withType(): KeyerWithType<T> =
    KeyerWithType(T::class, this)
