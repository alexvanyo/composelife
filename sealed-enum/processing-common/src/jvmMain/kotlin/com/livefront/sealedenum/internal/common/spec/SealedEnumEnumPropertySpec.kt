package com.livefront.sealedenum.internal.common.spec

import com.livefront.sealedenum.internal.common.Visibility
import com.squareup.kotlinpoet.ClassName
import com.squareup.kotlinpoet.FunSpec
import com.squareup.kotlinpoet.PropertySpec
import com.squareup.kotlinpoet.TypeName
import javax.lang.model.element.TypeElement

internal data class SealedEnumEnumPropertySpec(
    private val sealedClassVisibility: Visibility,
    private val parameterizedSealedClass: TypeName,
    private val sealedClassCompanionObjectElement: TypeElement?,
    private val sealedEnum: ClassName,
    private val enumForSealedEnum: ClassName,
    private val enumPrefix: String
) {
    fun build(): PropertySpec {
        val propertySpecBuilder = PropertySpec.builder(pascalCaseToCamelCase(enumPrefix + "Enum"), enumForSealedEnum)
            .maybeAddOriginatingElement(sealedClassCompanionObjectElement)
            .addKdoc("The isomorphic [%T] for [this].", enumForSealedEnum)
            .receiver(parameterizedSealedClass)
            .addModifiers(sealedClassVisibility.kModifier)
            .getter(
                FunSpec.getterBuilder()
                    .addStatement("return %T.sealedObjectToEnum(this)", sealedEnum)
                    .build()
            )

        return propertySpecBuilder.build()
    }
}
