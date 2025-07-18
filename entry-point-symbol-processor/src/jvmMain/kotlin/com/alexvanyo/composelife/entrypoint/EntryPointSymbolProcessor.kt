/*
 * Copyright 2025 The Android Open Source Project
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

package com.alexvanyo.composelife.entrypoint

import com.google.devtools.ksp.getVisibility
import com.google.devtools.ksp.processing.CodeGenerator
import com.google.devtools.ksp.processing.KSPLogger
import com.google.devtools.ksp.processing.Resolver
import com.google.devtools.ksp.processing.SymbolProcessor
import com.google.devtools.ksp.symbol.ClassKind
import com.google.devtools.ksp.symbol.KSAnnotated
import com.google.devtools.ksp.symbol.KSClassDeclaration
import com.google.devtools.ksp.symbol.KSDeclaration
import com.google.devtools.ksp.symbol.KSNode
import com.google.devtools.ksp.symbol.KSType
import com.google.devtools.ksp.symbol.Visibility
import com.squareup.kotlinpoet.AnnotationSpec
import com.squareup.kotlinpoet.ClassName
import com.squareup.kotlinpoet.FileSpec
import com.squareup.kotlinpoet.FunSpec
import com.squareup.kotlinpoet.KModifier
import com.squareup.kotlinpoet.LambdaTypeName
import com.squareup.kotlinpoet.ParameterSpec
import com.squareup.kotlinpoet.ParameterizedTypeName.Companion.parameterizedBy
import com.squareup.kotlinpoet.PropertySpec
import com.squareup.kotlinpoet.TypeSpec
import com.squareup.kotlinpoet.TypeVariableName
import com.squareup.kotlinpoet.WildcardTypeName
import com.squareup.kotlinpoet.asTypeName
import com.squareup.kotlinpoet.ksp.addOriginatingKSFile
import com.squareup.kotlinpoet.ksp.toAnnotationSpec
import com.squareup.kotlinpoet.ksp.toClassName
import com.squareup.kotlinpoet.ksp.toTypeName
import com.squareup.kotlinpoet.ksp.toTypeParameterResolver
import com.squareup.kotlinpoet.ksp.writeTo
import dev.zacsweers.metro.ClassKey
import dev.zacsweers.metro.ContributesBinding
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.Inject
import dev.zacsweers.metro.IntoMap
import dev.zacsweers.metro.MapKey
import dev.zacsweers.metro.Provider
import dev.zacsweers.metro.Provides
import kotlin.reflect.KClass

@OptIn(InternalEntryPointProviderApi::class)
class EntryPointSymbolProcessor(
    private val codeGenerator: CodeGenerator,
    private val logger: KSPLogger,
) : SymbolProcessor {
    override fun process(resolver: Resolver): List<KSAnnotated> = with(logger) {
        resolver
            .getSymbolsWithAnnotation(requireNotNull(EntryPoint::class.qualifiedName))
            .filterIsInstance<KSClassDeclaration>()
            .onEach {
                checkIsInterface(it) { "Contributed entry points must be interfaces." }
                checkIsPublic(it) { "Contributed entry points must be public." }
            }
            .forEach {
                generateEntryPointImplementation(it)
            }

        emptyList()
    }

    private fun generateEntryPointImplementation(entryPoint: KSClassDeclaration) {
        val entryPointImplClassName =
            entryPoint.toClassName().peerClass(entryPoint.simpleName.asString() + "Impl")
        val scopeClassName =
            requireNotNull(
                entryPoint
                    .annotations
                    .first { it.annotationType.toTypeName() == EntryPoint::class.asTypeName() }
                    .arguments
                    .first()
                    .value as KSType?
            ).toClassName()

        val fileSpec = FileSpec.builder(entryPointImplClassName)
            .addType(
                TypeSpec
                    .classBuilder(entryPointImplClassName)
                    .addOriginatingKSFile(requireNotNull(entryPoint.containingFile))
                    .addAnnotation(Inject::class)
                    .addAnnotation(
                        AnnotationSpec.builder(ContributesBinding::class)
                            .addMember("scope = %T::class", scopeClassName)
                            .build(),
                    )
                    .addSuperinterface(entryPoint.toClassName())
                    .primaryConstructor(
                        FunSpec.constructorBuilder()
                            .addParameters(
                                entryPoint.getAllProperties()
                                    .map { propertyDeclaration ->
                                        ParameterSpec.builder(
                                            name = propertyDeclaration.simpleName.asString(),
                                            type = propertyDeclaration.type.toTypeName(
                                                entryPoint.typeParameters.toTypeParameterResolver()
                                            )
                                                .copy(
                                                    annotations = propertyDeclaration.type.annotations
                                                        .map { it.toAnnotationSpec() }.toList()
                                                )

                                        )
                                            .addAnnotations(
                                                propertyDeclaration.annotations
                                                    .map { it.toAnnotationSpec() }.toList()
                                            )
                                            .build()
                                    }
                                    .toList()
                            )

                            .build(),
                    )
                    .addProperties(
                        entryPoint.getAllProperties()
                            .map { propertyDeclaration ->
                                PropertySpec.builder(
                                    name = propertyDeclaration.simpleName.asString(),
                                    type = propertyDeclaration.type.toTypeName(
                                        entryPoint.typeParameters.toTypeParameterResolver()
                                    )
                                        .copy(
                                            annotations = propertyDeclaration.type.annotations
                                                .map { it.toAnnotationSpec() }.toList()
                                        )
                                )
                                    .addAnnotations(
                                        propertyDeclaration.annotations
                                            .map { it.toAnnotationSpec() }.toList()
                                    )
                                    .addModifiers(KModifier.OVERRIDE)
                                    .initializer(propertyDeclaration.simpleName.asString())
                                    .build()
                            }
                            .toList()
                    )
                    .build(),
            )
            .addType(
                TypeSpec
                    .interfaceBuilder(entryPointImplClassName.peerClass(entryPointImplClassName.simpleName + "BindingComponent"))
                    .addAnnotation(
                        AnnotationSpec.builder(ContributesTo::class)
                            .addMember("scope = %T::class", scopeClassName)
                            .build(),
                    )
                    .addFunction(
                        FunSpec.builder("provides${entryPoint.simpleName.asString()}IntoEntryPointMap")
                            .addAnnotation(Provides::class)
                            .addAnnotation(IntoMap::class)
                            .addAnnotation(
                                AnnotationSpec.builder(ClassKey::class)
                                    .addMember("%T::class", entryPoint.toClassName())
                                    .build()
                            )
                            .addAnnotation(
                                AnnotationSpec.builder(ClassName("kotlin", "OptIn"))
                                    .addMember("%T::class", InternalEntryPointProviderApi::class)
                                    .build(),
                            )
                            .addParameter(
                                ParameterSpec.builder(
                                    "entryPointCreator",
                                    Provider::class.asTypeName().parameterizedBy(entryPoint.toClassName())
                                )
                                    .build()
                            )
                            .returns(
                                ScopedEntryPoint::class.asTypeName()
                                    .parameterizedBy(
                                        scopeClassName,
                                        WildcardTypeName.producerOf(
                                            Any::class.asTypeName().copy(nullable = true)
                                        )
                                    )
                            )
                            .addStatement(
                                "return %T(entryPointCreator)",
                                ScopedEntryPoint::class,
                            )
                            .build()
                    )
                    .build()
            )
            .addFunction(
                FunSpec.builder("getEntryPoint")
                    .addModifiers(KModifier.INLINE)
                    .addTypeVariable(TypeVariableName("T", entryPoint.toClassName()).copy(reified = true))
                    .addAnnotation(
                        AnnotationSpec.builder(ClassName("kotlin", "OptIn"))
                            .addMember("%T::class", InternalEntryPointProviderApi::class)
                            .build(),
                    )
                    .receiver(
                        EntryPointProvider::class.asTypeName().parameterizedBy(scopeClassName)
                    )
                    .addParameter(
                        ParameterSpec.builder("unused", KClass::class.asTypeName().parameterizedBy(TypeVariableName("T")))
                            .defaultValue("%T::class", TypeVariableName("T"))
                            .build()
                    )
                    .returns(entryPoint.toClassName())
                    .addStatement(
                        "return entryPoints.getValue(%T::class).entryPointCreator() as %T",
                        entryPoint.toClassName(),
                        entryPoint.toClassName(),
                    )
                    .build()
            )
            .build()

        fileSpec.writeTo(codeGenerator, aggregating = false)
    }
}

context(_: KSPLogger)
private fun checkIsInterface(
    clazz: KSClassDeclaration,
    lazyMessage: () -> String,
) {
    check(clazz.classKind == ClassKind.INTERFACE, clazz, lazyMessage)
}

context(_: KSPLogger)
private fun checkIsPublic(
    declaration: KSDeclaration,
    lazyMessage: () -> String,
) {
    check(declaration.getVisibility() == Visibility.PUBLIC, declaration, lazyMessage)
}

context(logger: KSPLogger)
private fun check(
    condition: Boolean,
    symbol: KSNode?,
    lazyMessage: () -> String,
) {
    if (!condition) {
        val message = lazyMessage()
        logger.error(message, symbol)
        throw IllegalStateException(message)
    }
}
