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

import androidx.compose.ui.test.ComposeUiTest
import androidx.compose.ui.test.ExperimentalTestApi
import com.alexvanyo.composelife.scopes.ApplicationComponent
import com.alexvanyo.composelife.scopes.UiComponent
import com.alexvanyo.composelife.scopes.UiComponentArguments
import com.alexvanyo.composelife.updatable.di.UpdatableModule
import kotlinx.coroutines.test.TestResult
import kotlinx.coroutines.test.TestScope

abstract class BaseUiInjectTest2<T, U>(
    applicationComponentCreator: () -> T,
    internal val uiComponentCreator: (T, UiComponentArguments) -> U,
) : BaseInjectTest<T>(applicationComponentCreator)
    where T : ApplicationComponent<*>, T : UpdatableModule, U : UiComponent<T, *>

@OptIn(ExperimentalTestApi::class)
expect fun <T, U> BaseUiInjectTest2<T, U>.runUiTest(
    testBody: suspend context(ComposeUiTest, TestScope) UiTestScope<T, U>.() -> Unit,
): TestResult where T : ApplicationComponent<*>, T : UpdatableModule, U : UiComponent<T, *>

interface UiTestScope<T, U> where T : ApplicationComponent<*>, T : UpdatableModule, U : UiComponent<T, *> {
    val uiComponent: U
}
