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

import software.amazon.lastmile.kotlin.inject.anvil.extend.ContributingAnnotation
import kotlin.reflect.KClass

/**
 * An annotation that identifies an entry point interface for the given [scope].
 *
 * This will generate a concrete implementation of the entry point interface, where each property of this interface
 * is provided for via constructor injection.
 *
 * Concretely,
 *
 * ```kotlin
 * @EntryPoint(AppScope::class)
 * interface MyEntryPoint : MyInheritedInterface {
 *     val myDependency: MyDependency
 * }
 * ```
 *
 * will generate
 *
 * ```kotlin
 * @Inject
 * @ContributesBinding(AppScope::class)
 * class MyEntryPointImpl(
 *     override val myDependency: MyDependency,
 *     override val myInheritedDependency: MyInheritedDependency // from MyInheritedInterface
 * ) : MyEntryPoint
 *
 * @ContributesTo(AppScope::class)
 * interface MyEntryPointImplBindingComponent {
 *     @Provides
 *     @IntoMap
 *     @OptIn(InternalEntryPointProviderApi::class)
 *     fun providesMyEntryPointIntoEntryPointMap(
 *         entryPointCreator: () -> MyEntryPoint
 *     ): Pair<KClass<*>, ScopedEntryPoint<AppScope, *>> =
 *         MyEntryPoint::class to ScopedEntryPoint(entryPointCreator)
 * }
 *
 * @OptIn(InternalEntryPointProviderApi::class)
 * inline fun <reified T : MyEntryPoint> EntryPointProvider<AppScope>.getEntryPoint(
 *     unused: KClass<T> = T::class
 * ): MyEntryPoint = entryPoints.getValue(MyEntryPoint::class).entryPointCreator() as MyEntryPoint
 * ```
 *
 * This allows safely retrieving an `MyEntryPoint` from the component that implements `EntryPointProvider<AppScope>`
 * with `applicationComponent.getEntryPoint<MyEntryPoint>()`.
 */
@Target(AnnotationTarget.CLASS)
@ContributingAnnotation
annotation class EntryPoint(
    /**
     * The marker that identifies this scope.
     */
    val scope: KClass<*>,
)
