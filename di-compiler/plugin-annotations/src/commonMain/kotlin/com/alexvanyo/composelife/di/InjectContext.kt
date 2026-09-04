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
 * - Metro generates an injectable class with the same name as the function (e.g., `Foo`), providing
 *   an `operator fun invoke(...)` that receives any `@Assisted` parameters and injects all context
 *   dependencies from the Metro dependency graph.
 * - The `di-compiler` plugin generates a top-level context function with the same name (`Foo`)
 *   that requires `context(ctx: Foo)` and accepts the `@Assisted` parameters. Overloads are generated for
 *   assisted parameters with default values. Any other annotations on the original function (such as `@Composable`)
 *   are preserved on the generated context function.
 * - The generated context function delegates in IR to `ctx.invoke(...)`.
 *
 * This allows call sites to invoke the function directly using standard context parameter resolution:
 * ```kotlin
 * context(foo: Foo)
 * fun Parent() {
 *     Foo(...)
 * }
 * ```
 */
@Target(FUNCTION)
annotation class InjectContext
