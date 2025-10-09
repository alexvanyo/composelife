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
import com.livefront.sealedenum.internal.common.Visibility
import com.squareup.kotlinpoet.ClassName
import com.squareup.kotlinpoet.FunSpec
import com.squareup.kotlinpoet.PropertySpec
import com.squareup.kotlinpoet.asTypeName
import javax.lang.model.element.TypeElement

internal data class SealedEnumSealedEnumPropertySpec(
    private val sealedClass: SealedClass,
    private val sealedClassCompanionObject: ClassName,
    private val sealedClassCompanionObjectEffectiveVisibility: Visibility,
    private val sealedClassCompanionObjectElement: TypeElement?,
    private val sealedEnum: ClassName,
    private val enumPrefix: String
) {
    fun build(): PropertySpec {
        val propertySpecBuilder = PropertySpec.builder(pascalCaseToCamelCase(enumPrefix + "SealedEnum"), sealedEnum)
            .maybeAddOriginatingElement(sealedClassCompanionObjectElement)
            .addKdoc(
                "Returns an implementation of [%T] for the sealed class [%T]",
                SealedEnum::class.asTypeName(), // Explicitly resolve to TypeName to avoid hitting javax.lang classes
                sealedClass
            )
            .receiver(sealedClassCompanionObject)
            .addModifiers(sealedClassCompanionObjectEffectiveVisibility.kModifier)
            .getter(
                FunSpec.getterBuilder()
                    .addStatement("return %T", sealedEnum)
                    .build()
            )

        return propertySpecBuilder.build()
    }
}
