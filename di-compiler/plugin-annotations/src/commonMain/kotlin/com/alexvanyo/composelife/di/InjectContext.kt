/*
 * Copyright 2026 The Android Open Source Project
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

package com.alexvanyo.composelife.di

import kotlin.annotation.AnnotationTarget.FUNCTION

/**
 * Annotation to mark a function for dependency injection with context parameters.
 *
 * When applied to a top-level function alongside `@Inject`, the `di-compiler` plugin
 * collaborates with Metro to generate convenient context functions.
 *
 * Specifically:
 * - Metro generates an injectable class with the same name as the function (e.g., `ParentComponent`), providing
 *   an `operator fun invoke(...)` that receives any `@Assisted` parameters and injects all context
 *   and normal dependencies from the Metro dependency graph.
 * - The `di-compiler` plugin generates matching top-level context functions with the same name (`ParentComponent`)
 *   that require `context(ctx: ParentComponent)` and accept the `@Assisted` parameters. Overloads are generated for
 *   assisted parameters with default values so callers can omit them. Any other annotations on the original function
 *   (such as `@Composable`) are preserved on the generated context functions.
 * - The generated context function delegates in IR to `ctx.invoke(...)`.
 *
 * ### Example
 *
 * Given a function that has context parameters for a nested function call (`ChildComponent`), a normal injection
 * parameter (`Repository`), and an assisted parameter (`modifier`):
 *
 * ```kotlin
 * @InjectContext
 * @Inject
 * @Composable
 * context(
 *     _: ChildComponent,
 * )
 * fun ParentComponent(
 *     repository: Repository,
 *     @Assisted modifier: Modifier = Modifier,
 * ) {
 *     ChildComponent()
 *     // use repository and modifier...
 * }
 * ```
 *
 * #### What Metro generates
 * Metro generates an injectable class containing constructor parameters for both the context parameter dependencies
 * and normal injection parameters, with an `invoke` operator taking the assisted parameter:
 *
 * ```kotlin
 * @Inject
 * class ParentComponent(
 *     private val childComponent: ChildComponent,
 *     private val repository: Repository,
 * ) {
 *     @Composable
 *     operator fun invoke(
 *         modifier: Modifier = Modifier,
 *     ) {
 *         context(childComponent) {
 *             ParentComponent(
 *                 repository = repository,
 *                 modifier = modifier,
 *             )
 *         }
 *     }
 * }
 * ```
 *
 * #### What di-compiler generates
 * The `di-compiler` plugin generates top-level context functions that require `context(ctx: ParentComponent)`,
 * including overloads for assisted parameters with default values:
 *
 * ```kotlin
 * context(ctx: ParentComponent)
 * @Composable
 * fun ParentComponent(
 *     modifier: Modifier = Modifier,
 * ) {
 *     ctx.invoke(
 *         modifier = modifier,
 *     )
 * }
 *
 * context(ctx: ParentComponent)
 * @Composable
 * fun ParentComponent() {
 *     ctx.invoke()
 * }
 * ```
 *
 * #### Usage at call sites
 * Call sites only need the generated context class in their context:
 *
 * ```kotlin
 * context(_: ParentComponent)
 * @Composable
 * fun GrandparentComponent() {
 *     ParentComponent()
 * }
 * ```
 */
@Target(FUNCTION)
annotation class InjectContext
