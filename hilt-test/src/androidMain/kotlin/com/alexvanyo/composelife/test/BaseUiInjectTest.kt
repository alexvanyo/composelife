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

import android.content.Context
import android.os.Build
import androidx.activity.ComponentActivity
import androidx.compose.ui.test.junit4.createAndroidComposeRule
import com.alexvanyo.composelife.kmpandroidrunner.KmpAndroidJUnit4
import com.alexvanyo.composelife.scopes.ApplicationComponent
import com.alexvanyo.composelife.updatable.di.UpdatableModule
import kotlinx.coroutines.test.runTest
import leakcanary.DetectLeaksAfterTestSuccess
import org.junit.Rule
import org.junit.rules.TestRule
import org.junit.runner.RunWith

/**
 * A base class for testing components that depend on injected classes.
 *
 * Subclasses must call [runAppTest] instead of [runTest] to properly initialize dependencies.
 */
@Suppress("UnnecessaryAbstractClass")
@RunWith(KmpAndroidJUnit4::class)
abstract class BaseUiInjectTest<T, A : ComponentActivity>(
    applicationComponentCreator: () -> T,
    clazz: Class<A>,
) : BaseInjectTest<T>(applicationComponentCreator) where T : ApplicationComponent, T : UpdatableModule {

    @get:Rule(order = 0)
    val outerLeakRule = createLeakRule("Outer")

    @get:Rule(order = 2)
    val composeTestRule = createAndroidComposeRule(clazz)

    @get:Rule(order = 3)
    val innerLeakRule = createLeakRule("Inner")

    val context: Context get() = composeTestRule.activity
}

private fun createLeakRule(tag: String) =
    if (Build.FINGERPRINT.lowercase() == "robolectric") {
        TestRule { base, _ -> base }
    } else {
        DetectLeaksAfterTestSuccess(tag)
    }
