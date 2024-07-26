/*
 * Copyright 2024 The Android Open Source Project
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

package com.alexvanyo.composelife.test

import androidx.activity.ComponentActivity
import androidx.compose.ui.test.ComposeUiTest
import androidx.compose.ui.test.ExperimentalTestApi
import androidx.compose.ui.test.runAndroidComposeUiTest
import com.alexvanyo.composelife.scopes.ApplicationComponent
import com.alexvanyo.composelife.scopes.UiComponent
import com.alexvanyo.composelife.scopes.UiComponentArguments
import com.alexvanyo.composelife.updatable.di.UpdatableModule
import kotlinx.coroutines.test.TestResult
import kotlinx.coroutines.test.TestScope
import kotlin.coroutines.CoroutineContext

@OptIn(ExperimentalTestApi::class)
actual fun <T, U> BaseUiInjectTest<T, U>.runUiTest(
    appTestContext: CoroutineContext,
    testBody: suspend context(ComposeUiTest, TestScope) UiTestScope<T, U>.() -> Unit,
): TestResult where T : ApplicationComponent<*>, T : UpdatableModule, U : UiComponent<T, *> =
    runAndroidComposeUiTest<ComponentActivity> {
        val uiComponent = uiComponentCreator(
            applicationComponent,
            object : UiComponentArguments {
                override val activity = requireNotNull(this@runAndroidComposeUiTest.activity)
            },
        )

        runAppTest(appTestContext) {
            testBody(
                this,
                object : UiTestScope<T, U> {
                    override val uiComponent = uiComponent
                },
            )
        }
    }
