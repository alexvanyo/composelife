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

import com.livefront.sealedenum.internal.common.Visibility
import com.squareup.kotlinpoet.ClassName
import com.squareup.kotlinpoet.FunSpec
import com.squareup.kotlinpoet.TypeName
import javax.lang.model.element.TypeElement

internal data class SealedEnumValueOfFunSpec(
    private val sealedClass: SealedClass,
    private val parameterizedSealedClass: TypeName,
    private val sealedClassCompanionObject: ClassName,
    private val sealedClassCompanionObjectEffectiveVisibility: Visibility,
    private val sealedClassCompanionObjectElement: TypeElement?,
    private val sealedEnum: ClassName,
    private val enumPrefix: String
) {
    fun build(): FunSpec {
        val funSpecBuilder = FunSpec.builder(pascalCaseToCamelCase(enumPrefix + "ValueOf"))
            .maybeAddOriginatingElement(sealedClassCompanionObjectElement)
            .addKdoc(
                """
                Returns the [%T] object for the given [name].
                
                If the given name doesn't correspond to any [%T], an [IllegalArgumentException] will be thrown.
                """.trimIndent(),
                sealedClass,
                sealedClass
            )
            .receiver(sealedClassCompanionObject)
            .addModifiers(sealedClassCompanionObjectEffectiveVisibility.kModifier)
            .returns(parameterizedSealedClass)
            .addParameter("name", String::class)
            .addStatement("return %T.valueOf(name)", sealedEnum)

        return funSpecBuilder.build()
    }
}
