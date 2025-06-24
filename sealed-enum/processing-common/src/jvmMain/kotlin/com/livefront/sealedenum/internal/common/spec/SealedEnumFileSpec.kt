package com.livefront.sealedenum.internal.common.spec

import com.livefront.sealedenum.SealedEnum
import com.livefront.sealedenum.TreeTraversalOrder
import com.livefront.sealedenum.internal.common.SealedClassNode
import com.livefront.sealedenum.internal.common.Visibility
import com.livefront.sealedenum.internal.common.getSealedObjectsFromNode
import com.squareup.kotlinpoet.ClassName
import com.squareup.kotlinpoet.FileSpec
import com.squareup.kotlinpoet.ParameterizedTypeName.Companion.parameterizedBy
import com.squareup.kotlinpoet.TypeName
import javax.lang.model.element.TypeElement

/**
 * A builder for a file containing implementations of [SealedEnum] for the given [sealedClass].
 *
 * Given the [ClassName] for [sealedClass], the [TypeElement] for the [sealedClassCompanionObjectElement], and the
 * [sealedClassNode] representing the tree of objects for the [sealedClass], [build] will create a [FileSpec] with
 * generated classes given the [sealedEnumOptions].
 *
 * The generated file will be the name of the sealed class, suffixed with "_SealedEnum".
 *
 * If the sealed class is generic, pass in the the sanitized type parameters as [typeParameters]. The resulting
 * [SealedEnum] object use these specifications to parameterize the [sealedClass].
 */
public data class SealedEnumFileSpec(
    private val sealedClass: ClassName,
    private val sealedClassVisibility: Visibility,
    private val sealedClassCompanionObject: ClassName,
    private val sealedClassCompanionObjectVisibility: Visibility,
    private val sealedClassCompanionObjectElement: TypeElement?,
    private val sealedClassNode: SealedClassNode.SealedClass,
    private val typeParameters: List<TypeName>,
    private val sealedEnumOptions: Map<TreeTraversalOrder, SealedEnumOption>
) {

    /**
     * Determines the effective visibility of the companion object based on the companion object's visibility and the
     * sealed class's visibility. If either are internal, than the effective visibility is internal.
     */
    private val sealedClassCompanionObjectEffectiveVisibility = when (sealedClassCompanionObjectVisibility) {
        Visibility.PUBLIC -> when (sealedClassVisibility) {
            Visibility.INTERNAL -> Visibility.INTERNAL
            Visibility.PUBLIC -> Visibility.PUBLIC
        }
        Visibility.INTERNAL -> Visibility.INTERNAL
    }

    public fun build(): FileSpec {
        val fileName = "${sealedClass.simpleNames.joinToString(".")}_SealedEnum"
        val fileSpecBuilder = FileSpec.builder(sealedClass.packageName, fileName).indent("    ")

        val parameterizedSealedClass = if (typeParameters.isEmpty()) {
            sealedClass
        } else {
            sealedClass.parameterizedBy(typeParameters)
        }

        sealedEnumOptions.forEach { (treeTraversalOrder, sealedEnumOption) ->
            val sealedObjects = getSealedObjectsFromNode(treeTraversalOrder, sealedClassNode)

            val enumPrefix = if (sealedEnumOptions.size == 1) {
                ""
            } else {
                when (treeTraversalOrder) {
                    TreeTraversalOrder.PRE_ORDER -> "PreOrder"
                    TreeTraversalOrder.IN_ORDER -> "InOrder"
                    TreeTraversalOrder.POST_ORDER -> "PostOrder"
                    TreeTraversalOrder.LEVEL_ORDER -> "LevelOrder"
                }
            }

            val sealedEnumTypeSpecBuilder = SealedEnumTypeSpec(
                sealedClass = sealedClass,
                sealedClassVisibility = sealedClassVisibility,
                parameterizedSealedClass = parameterizedSealedClass,
                sealedClassCompanionObjectElement = sealedClassCompanionObjectElement,
                sealedObjects = sealedObjects,
                enumPrefix = enumPrefix
            )

            val sealedEnumClassName = ClassName(sealedClass.packageName, sealedEnumTypeSpecBuilder.name)

            when (sealedEnumOption) {
                is SealedEnumOption.SealedEnumOnly -> Unit
                is SealedEnumOption.SealedEnumWithEnum ->
                    addEnumTypeSpec(
                        parameterizedSealedClass,
                        sealedObjects,
                        enumPrefix,
                        sealedEnumOption,
                        fileSpecBuilder,
                        sealedEnumTypeSpecBuilder,
                        sealedEnumClassName
                    )
            }

            val sealedEnumTypeSpec = sealedEnumTypeSpecBuilder.build()

            fileSpecBuilder.addType(sealedEnumTypeSpec)

            addExtensions(fileSpecBuilder, parameterizedSealedClass, sealedEnumClassName, enumPrefix)
        }

        return fileSpecBuilder.build()
    }

    /**
     * Adds an isomorphic enum type spec.
     */
    @Suppress("LongParameterList")
    private fun addEnumTypeSpec(
        parameterizedSealedClass: TypeName,
        sealedObjects: List<ClassName>,
        enumPrefix: String,
        sealedEnumOption: SealedEnumOption.SealedEnumWithEnum,
        fileSpecBuilder: FileSpec.Builder,
        sealedEnumTypeSpecBuilder: SealedEnumTypeSpec,
        sealedEnumClassName: ClassName
    ) {
        val enumForSealedEnumTypeSpec = EnumForSealedEnumTypeSpec(
            sealedClass = sealedClass,
            sealedClassVisibility = sealedClassVisibility,
            parameterizedSealedClass = parameterizedSealedClass,
            sealedClassCompanionObjectElement = sealedClassCompanionObjectElement,
            sealedObjects = sealedObjects,
            enumPrefix = enumPrefix,
            sealedClassInterfaces = sealedEnumOption.sealedClassInterfaces
        )
            .build()

        fileSpecBuilder.addType(enumForSealedEnumTypeSpec)

        @Suppress("UnsafeCallOnNullableType") // Generated enum will have a non-null name
        val enumForSealedEnumClassName =
            ClassName(sealedClass.packageName, enumForSealedEnumTypeSpec.name!!)

        sealedEnumTypeSpecBuilder.addEnumForSealedEnumProvider(enumForSealedEnumClassName)

        // Add the SealedClass.enum extension property
        fileSpecBuilder.addProperty(
            SealedEnumEnumPropertySpec(
                sealedClassVisibility = sealedClassVisibility,
                parameterizedSealedClass = parameterizedSealedClass,
                sealedClassCompanionObjectElement = sealedClassCompanionObjectElement,
                sealedEnum = sealedEnumClassName,
                enumForSealedEnum = enumForSealedEnumClassName,
                enumPrefix = enumPrefix
            )
                .build()
        )

        // Add the SealedClassEnum.sealedObject extension property
        fileSpecBuilder.addProperty(
            EnumSealedObjectPropertySpec(
                sealedClass = sealedClass,
                sealedClassVisibility = sealedClassVisibility,
                parameterizedSealedClass = parameterizedSealedClass,
                sealedClassCompanionObjectElement = sealedClassCompanionObjectElement,
                sealedEnum = sealedEnumClassName,
                enumForSealedEnum = enumForSealedEnumClassName
            )
                .build()
        )
    }

    /**
     * Adds extension properties and functions for the sealed class types.
     */
    private fun addExtensions(
        fileSpecBuilder: FileSpec.Builder,
        parameterizedSealedClass: TypeName,
        sealedEnumClassName: ClassName,
        enumPrefix: String
    ) {
        // Add the SealedEnum.ordinal extension property
        fileSpecBuilder.addProperty(
            SealedEnumOrdinalPropertySpec(
                sealedClassVisibility = sealedClassVisibility,
                parameterizedSealedClass = parameterizedSealedClass,
                sealedClassCompanionObjectElement = sealedClassCompanionObjectElement,
                sealedEnum = sealedEnumClassName,
                enumPrefix = enumPrefix
            )
                .build()
        )

        // Add the SealedEnum.name extension property
        fileSpecBuilder.addProperty(
            SealedEnumNamePropertySpec(
                sealedClassVisibility = sealedClassVisibility,
                parameterizedSealedClass = parameterizedSealedClass,
                sealedClassCompanionObjectElement = sealedClassCompanionObjectElement,
                sealedEnum = sealedEnumClassName,
                enumPrefix = enumPrefix
            )
                .build()
        )

        // Add the SealedEnum.Companion.values extension property
        fileSpecBuilder.addProperty(
            SealedEnumValuesPropertySpec(
                sealedClass = sealedClass,
                parameterizedSealedClass = parameterizedSealedClass,
                sealedClassCompanionObject = sealedClassCompanionObject,
                sealedClassCompanionObjectEffectiveVisibility = sealedClassCompanionObjectEffectiveVisibility,
                sealedClassCompanionObjectElement = sealedClassCompanionObjectElement,
                sealedEnum = sealedEnumClassName,
                enumPrefix = enumPrefix
            )
                .build()
        )

        // Add the SealedEnum.Companion.sealedEnum extension property
        fileSpecBuilder.addProperty(
            SealedEnumSealedEnumPropertySpec(
                sealedClass = sealedClass,
                sealedClassCompanionObject = sealedClassCompanionObject,
                sealedClassCompanionObjectEffectiveVisibility = sealedClassCompanionObjectEffectiveVisibility,
                sealedClassCompanionObjectElement = sealedClassCompanionObjectElement,
                sealedEnum = sealedEnumClassName,
                enumPrefix = enumPrefix
            )
                .build()
        )

        // Add the SealedEnum.Companion.valueOf extension function
        fileSpecBuilder.addFunction(
            SealedEnumValueOfFunSpec(
                sealedClass = sealedClass,
                parameterizedSealedClass = parameterizedSealedClass,
                sealedClassCompanionObject = sealedClassCompanionObject,
                sealedClassCompanionObjectEffectiveVisibility = sealedClassCompanionObjectEffectiveVisibility,
                sealedClassCompanionObjectElement = sealedClassCompanionObjectElement,
                sealedEnum = sealedEnumClassName,
                enumPrefix = enumPrefix
            )
                .build()
        )
    }

    /**
     * The options for generating classes for a [TreeTraversalOrder].
     */
    public sealed class SealedEnumOption {
        /**
         * Generate the [SealedEnum] only.
         */
        public object SealedEnumOnly : SealedEnumOption()

        /**
         * Generate the [SealedEnum] and a isomorphic enum class.
         */
        public data class SealedEnumWithEnum(
            val sealedClassInterfaces: List<TypeName>
        ) : SealedEnumOption()
    }
}
