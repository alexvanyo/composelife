package com.livefront.sealedenum.internal.common.spec

import com.livefront.sealedenum.EnumForSealedEnumProvider
import com.livefront.sealedenum.SealedEnum
import com.livefront.sealedenum.SealedEnumWithEnumProvider
import com.livefront.sealedenum.internal.common.Visibility
import com.squareup.kotlinpoet.ClassName
import com.squareup.kotlinpoet.FunSpec
import com.squareup.kotlinpoet.KModifier
import com.squareup.kotlinpoet.ParameterizedTypeName.Companion.parameterizedBy
import com.squareup.kotlinpoet.PropertySpec
import com.squareup.kotlinpoet.TypeName
import com.squareup.kotlinpoet.TypeSpec
import com.squareup.kotlinpoet.asClassName
import com.squareup.kotlinpoet.asTypeName
import com.squareup.kotlinpoet.buildCodeBlock
import javax.lang.model.element.TypeElement
import kotlin.reflect.KClass

/**
 * A builder for a [SealedEnum] object for the given [sealedClass].
 *
 * Given the [ClassName] of the [sealedClass], the [TypeElement] for the [sealedClassCompanionObjectElement], and the
 * list of [ClassName]s for the sealed subclasses, [build] will generate a [TypeSpec] for an implementation of
 * [SealedEnum].
 *
 * Before calling [build], [addEnumForSealedEnumProvider] will additionally let the generated object implement
 * [EnumForSealedEnumProvider] and [SealedEnumWithEnumProvider] for the given enum.
 *
 * The name of the created object will be the name of the sealed class concatenated with [enumPrefix] concatenated with
 * "SealedEnum".
 */
internal data class SealedEnumTypeSpec(
    private val sealedClass: SealedClass,
    private val sealedClassVisibility: Visibility,
    private val parameterizedSealedClass: TypeName,
    private val sealedClassCompanionObjectElement: TypeElement?,
    private val sealedObjects: List<SealedObject>,
    private val enumPrefix: String
) {
    val name = sealedClass.createSealedEnumName(enumPrefix)
    private val listOfSealedClass = List::class.asClassName().parameterizedBy(parameterizedSealedClass)
    private val sealedEnum = SealedEnum::class.asClassName()
    private val parameterizedSealedClassEnum = sealedEnum.parameterizedBy(parameterizedSealedClass)
    private val typeSpecBuilder = TypeSpec.objectBuilder(name)
        .addModifiers(sealedClassVisibility.kModifier)
        .addSuperinterface(parameterizedSealedClassEnum)
        .maybeAddOriginatingElement(sealedClassCompanionObjectElement)
        .addKdoc("An implementation of [%T] for the sealed class [%T]", sealedEnum, sealedClass)
        .addProperty(createObjectsProperty())
        .addFunction(createOrdinalOfFunction())
        .addFunction(createNameOfFunction())
        .addFunction(createValueOfFunction())

    fun addEnumForSealedEnumProvider(
        enumForSealedEnum: ClassName
    ) {
        val enumForSealedEnumProvider = EnumForSealedEnumProvider::class.asClassName()
        val parameterizedEnumForSealedEnumProvider = enumForSealedEnumProvider.parameterizedBy(
            parameterizedSealedClass,
            enumForSealedEnum
        )
        val sealedEnumWithSealedEnumProvider = SealedEnumWithEnumProvider::class.asClassName()
        val parameterizedSealedEnumWithSealedEnumProvider = sealedEnumWithSealedEnumProvider.parameterizedBy(
            parameterizedSealedClass,
            enumForSealedEnum
        )

        typeSpecBuilder
            .addSuperinterface(parameterizedSealedEnumWithSealedEnumProvider)
            .addSuperinterface(parameterizedEnumForSealedEnumProvider)
            .addProperty(createEnumClassGetter(enumForSealedEnum))
            .addFunction(createSealedObjectToEnumFunction(enumForSealedEnum))
            .addFunction(createEnumToSealedObjectFunction(enumForSealedEnum))
    }

    fun build(): TypeSpec = typeSpecBuilder.build()

    private fun createObjectsProperty(): PropertySpec = PropertySpec.builder("values", listOfSealedClass)
        .addModifiers(KModifier.OVERRIDE)
        .delegate(
            buildCodeBlock {
                beginControlFlow("lazy(mode = %T.PUBLICATION)", LazyThreadSafetyMode::class.asTypeName())
                if (sealedObjects.isEmpty()) {
                    addStatement("emptyList()")
                } else {
                    addStatement("listOf(")
                    indent()
                    sealedObjects.dropLast(1).forEach {
                        addStatement("%T,", it)
                    }
                    addStatement("%T", sealedObjects.last())
                    unindent()
                    addStatement(")")
                }
                endControlFlow()
            }
        )
        .build()

    private fun createOrdinalOfFunction(): FunSpec = FunSpec.builder("ordinalOf")
        .addParameter("obj", parameterizedSealedClass)
        .addModifiers(KModifier.OVERRIDE)
        .returns(Int::class)
        .apply {
            if (sealedObjects.isEmpty()) {
                addStatement(
                    "throw AssertionError(%S)",
                    "Constructing a ${sealedClass.simpleName} is impossible, since it has no sealed subclasses"
                )
            } else {
                beginControlFlow("return when (obj)")
                sealedObjects.forEachIndexed { index, obj ->
                    addStatement("is %T -> $index", obj)
                }
                endControlFlow()
            }
        }
        .build()

    private fun sealedObjectToName(obj: ClassName): String =
        obj.simpleNames.joinToString("_")

    private fun createNameOfFunction(): FunSpec = FunSpec.builder("nameOf")
        .addParameter("obj", parameterizedSealedClass)
        .addModifiers(KModifier.OVERRIDE)
        .returns(String::class)
        .apply {
            if (sealedObjects.isEmpty()) {
                addStatement(
                    "throw AssertionError(%S)",
                    "Constructing a ${sealedClass.simpleName} is impossible, since it has no sealed subclasses"
                )
            } else {
                beginControlFlow("return when (obj)")
                sealedObjects.forEach { obj ->
                    addStatement("is %T -> %S", obj, sealedObjectToName(obj))
                }
                endControlFlow()
            }
        }
        .build()

    private fun createValueOfFunction(): FunSpec = FunSpec.builder("valueOf")
        .addParameter("name", String::class)
        .addModifiers(KModifier.OVERRIDE)
        .returns(parameterizedSealedClass)
        .apply {
            if (sealedObjects.isEmpty()) {
                addStatement(
                    "throw IllegalArgumentException(%P)",
                    "No sealed enum constant \$name"
                )
            } else {
                beginControlFlow("return when (name)")
                sealedObjects.forEach { obj ->
                    addStatement("%S -> %T", sealedObjectToName(obj), obj)
                }
                addStatement(
                    "else -> throw IllegalArgumentException(%P)",
                    "No sealed enum constant \$name"
                )
                endControlFlow()
            }
        }
        .build()

    private fun createSealedObjectToEnumFunction(enumForSealedEnum: ClassName): FunSpec =
        FunSpec.builder("sealedObjectToEnum")
            .addParameter("obj", parameterizedSealedClass)
            .addModifiers(KModifier.OVERRIDE)
            .returns(enumForSealedEnum)
            .apply {
                if (sealedObjects.isEmpty()) {
                    addStatement(
                        "throw AssertionError(%S)",
                        "Constructing a ${sealedClass.simpleName} is impossible, since it has no sealed subclasses"
                    )
                } else {
                    beginControlFlow("return when (obj)")
                    sealedObjects.forEach { obj ->
                        addStatement(
                            "is %T -> %T",
                            obj,
                            enumForSealedEnum.nestedClass(obj.simpleNames.joinToString("_"))
                        )
                    }
                    endControlFlow()
                }
            }
            .build()

    private fun createEnumToSealedObjectFunction(enumForSealedEnum: ClassName): FunSpec =
        FunSpec.builder("enumToSealedObject")
            .addParameter("enum", enumForSealedEnum)
            .addModifiers(KModifier.OVERRIDE)
            .returns(parameterizedSealedClass)
            .apply {
                if (sealedObjects.isEmpty()) {
                    addStatement(
                        "throw AssertionError(%S)",
                        "Constructing a ${sealedClass.simpleName} is impossible, since it has no sealed subclasses"
                    )
                } else {
                    beginControlFlow("return when (enum)")
                    sealedObjects.forEach { obj ->
                        addStatement(
                            "%T -> %T",
                            enumForSealedEnum.nestedClass(obj.createValueName()),
                            obj
                        )
                    }
                    endControlFlow()
                }
            }
            .build()

    private fun createEnumClassGetter(enumForSealedEnum: ClassName): PropertySpec {
        val parameterizedClass = KClass::class.asClassName().parameterizedBy(enumForSealedEnum)

        return PropertySpec.builder("enumClass", parameterizedClass)
            .addModifiers(KModifier.OVERRIDE)
            .getter(
                FunSpec.getterBuilder()
                    .addStatement("return %T::class", enumForSealedEnum)
                    .build()
            )
            .build()
    }
}
