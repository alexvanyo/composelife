/*
 * Copyright 2023 The Android Open Source Project
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

import com.alexvanyo.composelife.entrypoint.EntryPoint
import com.alexvanyo.composelife.entrypoint.EntryPointProvider
import com.alexvanyo.composelife.entrypoint.ScopedEntryPoint
import software.amazon.lastmile.kotlin.inject.anvil.AppScope
import software.amazon.lastmile.kotlin.inject.anvil.SingleIn
import kotlin.reflect.KClass

@SingleIn(AppScope::class)
expect abstract class ApplicationComponent : EntryPointProvider<AppScope> {
    abstract override val entryPoints: Map<KClass<*>, ScopedEntryPoint<AppScope, *>>
}

// TODO: Remove when it is possible to declare an empty binding map
//       https://github.com/evant/kotlin-inject/issues/249
@EntryPoint(AppScope::class)
interface EmptyAppScopeEntryPoint
