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
import com.squareup.kotlinpoet.CodeBlock
import com.squareup.kotlinpoet.FunSpec
import com.squareup.kotlinpoet.TypeName
import com.squareup.kotlinpoet.TypeSpec
import javax.lang.model.element.TypeElement

/**
 * A builder for an enum class for the given [sealedClass].
 *
 * Given the [ClassName] of the [sealedClass], the [TypeElement] for the [sealedClassCompanionObjectElement], and
 * the list of [ClassName]s for the sealed subclasses, [build] will generate a [TypeSpec] for an enum class.
 *
 * The name of the created enum class will be the name of the sealed class concatenated with [enumPrefix] concatenated
 * with "Enum".
 */
internal data class EnumForSealedEnumTypeSpec(
    private val sealedClass: SealedClass,
    private val sealedClassVisibility: Visibility,
    private val sealedClassCompanionObjectElement: TypeElement?,
    private val sealedObjects: List<SealedObject>,
    private val parameterizedSealedClass: TypeName,
    private val enumPrefix: String,
    private val sealedClassInterfaces: List<TypeName>
) {
    private val typeSpecBuilder = TypeSpec.enumBuilder(sealedClass.createEnumForSealedEnumName(enumPrefix))
        .addModifiers(sealedClassVisibility.kModifier)
        .maybeAddOriginatingElement(sealedClassCompanionObjectElement)
        .addKdoc("An isomorphic enum for the sealed class [%T]", sealedClass)
        .primaryConstructor(
            FunSpec.constructorBuilder()
                .apply {
                    if (sealedClassInterfaces.isNotEmpty()) {
                        // Only add the sealed object constructor parameter if it is needed to implement an interface
                        addParameter("sealedObject", parameterizedSealedClass)
                    }
                }
                .build()
        )
        .apply {
            sealedClassInterfaces.forEach {
                superinterfaces[it] = CodeBlock.of("sealedObject")
            }
            sealedObjects.forEach {
                addEnumConstant(
                    it.createValueName(),
                    TypeSpec.anonymousClassBuilder()
                        .apply {
                            if (sealedClassInterfaces.isNotEmpty()) {
                                // Only add the sealed object constructor parameter if it is needed to implement an
                                // interface
                                addSuperclassConstructorParameter(CodeBlock.of(it.canonicalName))
                            }
                        }
                        .build()
                )
            }
        }

    fun build(): TypeSpec = typeSpecBuilder.build()
}
