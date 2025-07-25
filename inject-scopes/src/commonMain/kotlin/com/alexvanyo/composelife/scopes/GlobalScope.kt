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

package com.alexvanyo.composelife.scopes

/**
 * A special scope that exists outside of the app scope.
 *
 * Nothing should be put into the [GlobalScope] directly, except for the [ApplicationGraph.Factory].
 *
 * This allows anywhere (especially tests) to create a simple `GlobalGraph`, and inject the accumulated
 * [ApplicationGraph], which is centrally defined in this module:
 *
 * ```kotlin
 * @DependencyGraph(GlobalScope::class, isExtendable = true)
 * interface GlobalGraph
 *
 * internal val globalGraph = createGraph<GlobalGraph>()
 *
 * val applicationGraphFactory = globalGraph.asContribution<ApplicationGraph.Factory>()
 * ```
 */
abstract class GlobalScope private constructor()
