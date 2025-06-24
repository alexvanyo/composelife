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
