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
