/*
 * Copyright 2020 Livefront
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

package com.livefront.sealedenum

import kotlin.reflect.KClass

/**
 * Defines a provider for interoperability between a [SealedEnum] for type [T] and a normal enum class [E].
 */
public interface EnumForSealedEnumProvider<T, E : Enum<E>> {
    /**
     * A mapping of the sealed object of type [T] to the enum constant of type [E]. Together with the inverse function
     * [enumToSealedObject], this is an isomorphism.
     */
    public fun sealedObjectToEnum(obj: T): E

    /**
     * A mapping of the enum constant of type [E] to the enum constant of type [T]. Together with the inverse function
     * [sealedObjectToEnum], this is an isomorphism.
     */
    public fun enumToSealedObject(enum: E): T

    /**
     * The class object for the enum.
     */
    public val enumClass: KClass<E>
}
