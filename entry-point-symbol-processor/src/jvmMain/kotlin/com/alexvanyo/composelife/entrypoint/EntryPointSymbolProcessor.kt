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
import com.squareup.kotlinpoet.FileSpec
import com.squareup.kotlinpoet.FunSpec
import com.squareup.kotlinpoet.KModifier
import com.squareup.kotlinpoet.ParameterSpec
import com.squareup.kotlinpoet.ParameterizedTypeName
import com.squareup.kotlinpoet.ParameterizedTypeName.Companion.parameterizedBy
import com.squareup.kotlinpoet.PropertySpec
import com.squareup.kotlinpoet.TypeName
import com.squareup.kotlinpoet.TypeSpec
import com.squareup.kotlinpoet.WildcardTypeName
import com.squareup.kotlinpoet.asTypeName
import com.squareup.kotlinpoet.ksp.addOriginatingKSFile
import com.squareup.kotlinpoet.ksp.toAnnotationSpec
import com.squareup.kotlinpoet.ksp.toClassName
import com.squareup.kotlinpoet.ksp.toTypeName
import com.squareup.kotlinpoet.ksp.toTypeParameterResolver
import com.squareup.kotlinpoet.ksp.writeTo
import me.tatarka.inject.annotations.Inject
import me.tatarka.inject.annotations.IntoMap
import me.tatarka.inject.annotations.Provides
import software.amazon.lastmile.kotlin.inject.anvil.ContributesBinding
import software.amazon.lastmile.kotlin.inject.anvil.ContributesTo
import kotlin.reflect.KClass

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
                            .addParameter(
                                ParameterSpec.builder("entryPoint", entryPoint.toClassName()).build()
                            )
                            .returns(
                                Pair::class.asTypeName()
                                    .parameterizedBy(
                                        KClass::class.asTypeName().parameterizedBy(
                                            WildcardTypeName.producerOf(
                                                Any::class.asTypeName().copy(nullable = true)
                                            )
                                        ),
                                        ScopedEntryPoint::class.asTypeName()
                                            .parameterizedBy(
                                                scopeClassName,
                                                WildcardTypeName.producerOf(
                                                    Any::class.asTypeName().copy(nullable = true)
                                                )
                                            )
                                    )
                            )
                            .addStatement(
                                "return %T::class to %T(entryPoint)",
                                entryPoint.toClassName(),
                                ScopedEntryPoint::class,
                            )
                            .build()
                    )
                    .build()
            )
            .addFunction(
                FunSpec.builder("getEntryPoint")
                    .receiver(
                        EntryPointProvider::class.asTypeName().parameterizedBy(scopeClassName)
                    )
                    .returns(entryPoint.toClassName())
                    .addStatement(
                        "return entryPoints.getValue(%T::class).entryPoint as %T",
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
