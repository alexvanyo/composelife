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

import com.alexvanyo.composelife.kmpandroidrunner.KmpAndroidJUnit4
import com.alexvanyo.composelife.preferences.di.ComposeLifePreferencesProvider
import com.alexvanyo.composelife.preferences.di.PreferencesModule
import com.alexvanyo.composelife.preferences.di.TestPreferencesComponent
import org.junit.runner.RunWith
import kotlin.test.Test
import kotlin.test.assertIs

@RunWith(KmpAndroidJUnit4::class)
class TestPreferencesComponentTest {

    private val composeLifeApplicationComponent = TestComposeLifeApplicationComponent.createComponent()

    @Test
    fun checkType() {
        assertIs<PreferencesModule>(composeLifeApplicationComponent)
        assertIs<TestPreferencesComponent>(composeLifeApplicationComponent)
        assertIs<ComposeLifePreferencesProvider>(composeLifeApplicationComponent)

        assertIs<ComposeLifePreferences>(composeLifeApplicationComponent.composeLifePreferences)
        assertIs<TestComposeLifePreferences>(composeLifeApplicationComponent.composeLifePreferences)
    }
}
