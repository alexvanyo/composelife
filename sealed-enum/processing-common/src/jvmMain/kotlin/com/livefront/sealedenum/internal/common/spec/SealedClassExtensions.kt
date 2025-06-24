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

package com.livefront.sealedenum.internal.common.spec

import com.livefront.sealedenum.SealedEnum
import com.squareup.kotlinpoet.ClassName

internal typealias SealedClass = ClassName

internal typealias SealedObject = ClassName

/**
 * Creates the name of the [SealedEnum] for the given [SealedClass] and [enumPrefix].
 *
 * Ex: `Outer.Inner` with an [enumPrefix] of `LevelOrder` produces `"Outer_InnerLevelOrderSealedEnum"`
 */
internal fun SealedClass.createSealedEnumName(enumPrefix: String): String =
    "${simpleNames.joinToString("_")}${enumPrefix}SealedEnum"

/**
 * Creates the name of the enum for the given [SealedClass] and [enumPrefix].
 *
 * Ex: `Outer.Inner` with an [enumPrefix] of `LevelOrder` produces `"Outer_InnerLevelOrderEnum"`
 */
internal fun SealedClass.createEnumForSealedEnumName(enumPrefix: String): String =
    "${simpleNames.joinToString("_")}${enumPrefix}Enum"

/**
 * Creates the name of an enum value for the given object which is a subclass of a [SealedEnum].
 *
 * Ex: `Outer.Inner.First` becomes `"Outer_Inner_First"`
 */
internal fun SealedObject.createValueName(): String =
    simpleNames.joinToString("_")
