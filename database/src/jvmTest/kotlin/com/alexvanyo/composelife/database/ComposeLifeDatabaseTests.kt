/*
 * Copyright 2022 The Android Open Source Project
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

package com.alexvanyo.composelife.database

import com.alexvanyo.composelife.scopes.ApplicationComponent
import com.alexvanyo.composelife.test.BaseInjectTest
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.asContribution
import kotlin.test.Test
import kotlin.test.assertIs

@ContributesTo(AppScope::class)
interface ComposeLifeDatabaseTestsEntryPoint {
    val composeLifeDatabase: ComposeLifeDatabase
}

// TODO: Replace with asContribution()
internal val ApplicationComponent.composeLifeDatabaseTestsEntryPoint: ComposeLifeDatabaseTestsEntryPoint get() =
    this as ComposeLifeDatabaseTestsEntryPoint

class ComposeLifeDatabaseTests : BaseInjectTest(
    globalGraph.asContribution<ApplicationComponent.Factory>()::create,
) {
    private val entryPoint get() = applicationComponent.composeLifeDatabaseTestsEntryPoint

    private val composeLifeDatabase get() = entryPoint.composeLifeDatabase

    @Test
    fun cell_state_dao_returns_valid_instance() = runAppTest {
        assertIs<CellStateQueries>(composeLifeDatabase.cellStateQueries)
    }
}
