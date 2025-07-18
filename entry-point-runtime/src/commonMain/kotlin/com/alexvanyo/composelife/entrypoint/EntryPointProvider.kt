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

import dev.zacsweers.metro.Multibinds
import kotlin.reflect.KClass

/**
 * A provider of [EntryPoint]s scoped to [S].
 *
 * [EntryPoint]s should not be retrieved directly, and should only be retrieved through the `getEntryPoint()`
 * function for each [EntryPoint] type that are generated as extension functions on [EntryPointProvider] for the
 * correct scope.
 */
interface EntryPointProvider<S : Any> {
    @Multibinds
    val entryPoints: Map<KClass<*>, ScopedEntryPoint<S, *>>
}
