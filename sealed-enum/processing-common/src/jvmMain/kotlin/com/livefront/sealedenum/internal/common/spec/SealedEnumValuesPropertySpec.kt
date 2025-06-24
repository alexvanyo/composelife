package com.livefront.sealedenum.internal.common.spec

import com.livefront.sealedenum.internal.common.Visibility
import com.squareup.kotlinpoet.ClassName
import com.squareup.kotlinpoet.FunSpec
import com.squareup.kotlinpoet.ParameterizedTypeName.Companion.parameterizedBy
import com.squareup.kotlinpoet.PropertySpec
import com.squareup.kotlinpoet.TypeName
import com.squareup.kotlinpoet.asClassName
import javax.lang.model.element.TypeElement

internal data class SealedEnumValuesPropertySpec(
    private val sealedClass: SealedClass,
    private val parameterizedSealedClass: TypeName,
    private val sealedClassCompanionObject: ClassName,
    private val sealedClassCompanionObjectEffectiveVisibility: Visibility,
    private val sealedClassCompanionObjectElement: TypeElement?,
    private val sealedEnum: ClassName,
    private val enumPrefix: String
) {
    private val listOfSealedClass = List::class.asClassName().parameterizedBy(parameterizedSealedClass)

    fun build(): PropertySpec {
        val propertySpecBuilder = PropertySpec.builder(pascalCaseToCamelCase(enumPrefix + "Values"), listOfSealedClass)
            .maybeAddOriginatingElement(sealedClassCompanionObjectElement)
            .addKdoc("A list of all [%T] objects.", sealedClass)
            .receiver(sealedClassCompanionObject)
            .addModifiers(sealedClassCompanionObjectEffectiveVisibility.kModifier)
            .getter(
                FunSpec.getterBuilder()
                    .addStatement("return %T.values", sealedEnum)
                    .build()
            )

        return propertySpecBuilder.build()
    }
}
