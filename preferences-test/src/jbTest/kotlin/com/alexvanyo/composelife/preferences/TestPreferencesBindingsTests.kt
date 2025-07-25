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

package com.alexvanyo.composelife.preferences

import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.scopes.ApplicationGraph
import com.alexvanyo.composelife.test.BaseInjectTest
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.asContribution
import kotlin.test.Test
import kotlin.test.assertIs

@ContributesTo(AppScope::class)
interface TestPreferencesBindingsTestsEntryPoint : ComposeLifePreferencesProvider

// TODO: Replace with asContribution()
internal val ApplicationGraph.testPreferencesBindingsTestsEntryPoint: TestPreferencesBindingsTestsEntryPoint get() =
    this as TestPreferencesBindingsTestsEntryPoint

class TestPreferencesBindingsTests : BaseInjectTest(
    { globalGraph.asContribution<ApplicationGraph.Factory>().create(it) },
) {
    private val entryPoint = applicationGraph.testPreferencesBindingsTestsEntryPoint

    @Test
    fun checkType() {
        assertIs<ComposeLifePreferences>(entryPoint.composeLifePreferences)
        assertIs<TestComposeLifePreferences>(entryPoint.composeLifePreferences)
    }
}
