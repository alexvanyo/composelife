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
