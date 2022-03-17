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

package com.alexvanyo.composelife.preferences

import android.app.Application
import androidx.test.core.app.ApplicationProvider
import org.junit.rules.TemporaryFolder
import org.junit.rules.TestRule
import org.junit.runner.Description
import org.junit.runners.model.Statement

/**
 * A [TestRule] for setting up preferences with a temporary, automatically cleaned-up file.
 *
 * This rule should be applied, and then the [fileProvider] should be bound to Dagger.
 */
class PreferencesRule : TestRule {
    private val temporaryFolder = TemporaryFolder(ApplicationProvider.getApplicationContext<Application>().cacheDir)

    override fun apply(base: Statement, description: Description): Statement =
        temporaryFolder.apply(base, description)

    /**
     * The [FileProvider] to bind to Dagger for storing the preferences in a temporary way.
     */
    val fileProvider: FileProvider = FileProvider { temporaryFolder.newFile("preferences.pb.tmp") }
}
