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

package com.alexvanyo.composelife

import com.alexvanyo.composelife.scopes.GlobalScope
import com.alexvanyo.composelife.ui.app.UiWithLoadedPreferencesScope
import com.alexvanyo.composelife.ui.app.UiWithLoadedPreferencesScopeBindings
import dev.zacsweers.metro.BindingContainer
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.DependencyGraph
import dev.zacsweers.metro.Provides
import dev.zacsweers.metro.createGraph

@DependencyGraph(GlobalScope::class)
interface GlobalGraph

internal val globalGraph = createGraph<GlobalGraph>()

@ContributesTo(UiWithLoadedPreferencesScope::class, replaces = [UiWithLoadedPreferencesScopeBindings::class])
@BindingContainer
interface TestLoadedComposeLifePreferencesHolderBindings {

    companion object {
        @Provides
        internal fun emptyProvides(): EmptyProvides = EmptyProvides()
    }
}

internal class EmptyProvides
