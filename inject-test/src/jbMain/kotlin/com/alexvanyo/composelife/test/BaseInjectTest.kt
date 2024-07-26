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

package com.alexvanyo.composelife.test

import com.alexvanyo.composelife.kmpandroidrunner.KmpAndroidJUnit4
import com.alexvanyo.composelife.scopes.ApplicationComponent
import com.alexvanyo.composelife.updatable.Updatable
import com.alexvanyo.composelife.updatable.di.UpdatableModule
import kotlinx.coroutines.launch
import kotlinx.coroutines.test.TestResult
import kotlinx.coroutines.test.TestScope
import kotlinx.coroutines.test.runTest
import org.junit.runner.RunWith
import kotlin.coroutines.CoroutineContext
import kotlin.coroutines.EmptyCoroutineContext

/**
 * A base class for testing components that depend on injected classes.
 *
 * Subclasses must call [runAppTest] instead of [runTest] to properly initialize dependencies.
 */
@Suppress("UnnecessaryAbstractClass")
@RunWith(KmpAndroidJUnit4::class)
abstract class BaseInjectTest<T>(
    applicationComponentCreator: () -> T,
) where T : ApplicationComponent<*>, T : UpdatableModule {

    val applicationComponent: T = applicationComponentCreator()

    private val updatables: Set<Updatable>
        get() = applicationComponent.updatables

    open fun runAppTest(
        context: CoroutineContext = EmptyCoroutineContext,
        testBody: suspend TestScope.() -> Unit,
    ): TestResult = runTest(
        context = context,
    ) {
        updatables.forEach { updatable ->
            backgroundScope.launch {
                updatable.update()
            }
        }
        testBody()
    }
}
