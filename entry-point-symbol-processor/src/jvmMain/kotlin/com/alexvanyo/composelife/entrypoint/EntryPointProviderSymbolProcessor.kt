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
import com.google.devtools.ksp.processing.Resolver
import com.google.devtools.ksp.processing.SymbolProcessor
import com.google.devtools.ksp.symbol.KSAnnotated
import com.google.devtools.ksp.symbol.KSClassDeclaration
import com.google.devtools.ksp.symbol.KSType
import com.squareup.kotlinpoet.ParameterizedTypeName
import com.squareup.kotlinpoet.ParameterizedTypeName.Companion.parameterizedBy
import com.squareup.kotlinpoet.asClassName
import com.squareup.kotlinpoet.asTypeName
import com.squareup.kotlinpoet.ksp.toClassName
import com.squareup.kotlinpoet.ksp.toTypeName
import com.squareup.kotlinpoet.ksp.toTypeParameterResolver
import dev.zacsweers.metro.DependencyGraph

class EntryPointProviderSymbolProcessor : SymbolProcessor {
    override fun process(resolver: Resolver): List<KSAnnotated> =
        resolver
            .getSymbolsWithAnnotation(requireNotNull(DependencyGraph::class.qualifiedName))
            .filterIsInstance<KSClassDeclaration>()
            .filter { component ->
                val mergeScopeClassName =
                    (component
                        .annotations
                        .first { it.annotationType.toTypeName() == DependencyGraph::class.asTypeName() }
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
