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
