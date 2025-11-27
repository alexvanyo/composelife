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

package com.alexvanyo.composelife.navigation

import androidx.compose.runtime.Composable
import androidx.compose.runtime.remember
import androidx.compose.runtime.retain.RetainedValuesStoreRegistry
import androidx.compose.runtime.retain.retainRetainedValuesStoreRegistry
import androidx.navigation3.runtime.NavEntryDecorator

@Composable
public fun <T : Any> rememberRetainedValuesStoreNavEntryDecorator(
    retainedValuesStoreRegistry: RetainedValuesStoreRegistry = retainRetainedValuesStoreRegistry(),
): RetainedValuesStoreNavEntryDecorator<T> =
    remember(retainedValuesStoreRegistry) { RetainedValuesStoreNavEntryDecorator(retainedValuesStoreRegistry) }

public class RetainedValuesStoreNavEntryDecorator<T : Any>(
    retainedValuesStoreRegistry: RetainedValuesStoreRegistry,
) :
    NavEntryDecorator<T>(
        onPop = { contentKey -> retainedValuesStoreRegistry.clearChild(contentKey) },
        decorate = { entry ->
            retainedValuesStoreRegistry.LocalRetainedValuesStoreProvider(entry.contentKey) { entry.Content() }
        },
    )
