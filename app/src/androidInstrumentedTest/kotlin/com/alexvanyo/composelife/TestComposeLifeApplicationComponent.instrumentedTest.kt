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
@file:Suppress("MatchingDeclarationName")

package com.alexvanyo.composelife

import androidx.test.core.app.ApplicationProvider
import com.alexvanyo.composelife.test.TestInjectApplication

actual fun TestComposeLifeApplicationComponent.Companion.createComponent(): TestComposeLifeApplicationComponent {
    val application = ApplicationProvider.getApplicationContext<TestInjectApplication>()
    val applicationComponent = TestComposeLifeApplicationComponent.create(application)
    application.applicationComponent = applicationComponent
    application.uiComponentFactory = {
        TestComposeLifeUiComponent.create(applicationComponent, it.activity)
    }
    return applicationComponent
}
