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

import com.google.devtools.ksp.getAllSuperTypes
import com.google.devtools.ksp.getAnnotationsByType
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
import com.squareup.kotlinpoet.ParameterizedTypeName
import com.squareup.kotlinpoet.ParameterizedTypeName.Companion.parameterizedBy
import com.squareup.kotlinpoet.PropertySpec
import com.squareup.kotlinpoet.TypeName
import com.squareup.kotlinpoet.TypeSpec
import com.squareup.kotlinpoet.TypeVariableName
import com.squareup.kotlinpoet.WildcardTypeName
import com.squareup.kotlinpoet.asClassName
import com.squareup.kotlinpoet.asTypeName
import com.squareup.kotlinpoet.ksp.addOriginatingKSFile
import com.squareup.kotlinpoet.ksp.toAnnotationSpec
import com.squareup.kotlinpoet.ksp.toClassName
import com.squareup.kotlinpoet.ksp.toTypeName
import com.squareup.kotlinpoet.ksp.toTypeParameterResolver
import com.squareup.kotlinpoet.ksp.writeTo
import me.tatarka.inject.annotations.Component
import me.tatarka.inject.annotations.Inject
import me.tatarka.inject.annotations.IntoMap
import me.tatarka.inject.annotations.Provides
import software.amazon.lastmile.kotlin.inject.anvil.ContributesBinding
import software.amazon.lastmile.kotlin.inject.anvil.ContributesTo
import software.amazon.lastmile.kotlin.inject.anvil.MergeComponent
import kotlin.reflect.KClass

class EntryPointProviderSymbolProcessor : SymbolProcessor {
    override fun process(resolver: Resolver): List<KSAnnotated> =
        resolver
            .getSymbolsWithAnnotation(requireNotNull(Component::class.qualifiedName))
            .filterIsInstance<KSClassDeclaration>()
            .filter { component ->
                val mergeScopeClassName =
                    (component
                        .annotations
                        .first { it.annotationType.toTypeName() == MergeComponent::class.asTypeName() }
                        .arguments
                        .first()
                        .value as KSType?
                    )?.toClassName()

                if (mergeScopeClassName != null) {
                    try {
                        val entryPointProviderSuperType = component
                            .getAllSuperTypes()
                            .firstOrNull { superType ->
                                val superTypeName = superType.toTypeName(
                                    component.typeParameters.toTypeParameterResolver()
                                )
                                (superTypeName as? ParameterizedTypeName)?.rawType == EntryPointProvider::class.asClassName()
                            }

                        checkNotNull(entryPointProviderSuperType) {
                            "Component that is merging $mergeScopeClassName must implement " +
                                "EntryPointProvider<${mergeScopeClassName.simpleName}>"
                        }
                        val entryPointProviderSuperTypeName =entryPointProviderSuperType.toTypeName()
                        check(
                            entryPointProviderSuperTypeName == EntryPointProvider::class.asTypeName()
                                .parameterizedBy(mergeScopeClassName)
                        ) {
                            "Component that is merging $mergeScopeClassName must implement " +
                                "EntryPointProvider<${mergeScopeClassName.simpleName}> but instead implemented " +
                                "$entryPointProviderSuperTypeName"
                        }
                        false
                    } catch (exception: IllegalArgumentException) {
                        true
                    }
                } else {
                    false
                }
            }
            .toList()
}
