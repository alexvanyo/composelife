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

package com.alexvanyo.composelife.test

import android.content.Context
import android.os.Build
import androidx.activity.ComponentActivity
import androidx.compose.ui.test.junit4.createAndroidComposeRule
import androidx.test.ext.junit.runners.AndroidJUnit4
import com.alexvanyo.composelife.database.AppDatabase
import com.alexvanyo.composelife.preferences.ComposeLifePreferences
import com.alexvanyo.composelife.updatable.Updatable
import dagger.hilt.android.testing.HiltAndroidRule
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.launch
import kotlinx.coroutines.test.TestResult
import kotlinx.coroutines.test.TestScope
import kotlinx.coroutines.test.runTest
import leakcanary.DetectLeaksAfterTestSuccess
import org.junit.Rule
import org.junit.rules.TestRule
import org.junit.runner.RunWith
import javax.inject.Inject
import kotlin.test.AfterTest
import kotlin.test.BeforeTest

@Suppress("UnnecessaryAbstractClass")
@OptIn(ExperimentalCoroutinesApi::class)
@RunWith(AndroidJUnit4::class)
abstract class BaseHiltTest<T : ComponentActivity>(clazz: Class<T>) {

    @get:Rule(order = 0)
    val outerLeakRule = createLeakRule("Outer")

    @get:Rule(order = 1)
    val hiltAndroidRule = HiltAndroidRule(this)

    @get:Rule(order = 2)
    val composeTestRule = createAndroidComposeRule(clazz)

    @get:Rule(order = 3)
    val innerLeakRule = createLeakRule("Inner")

    @Inject
    lateinit var preferences: ComposeLifePreferences

    @Inject
    lateinit var appDatabase: AppDatabase

    @Inject
    lateinit var updatables: Set<@JvmSuppressWildcards Updatable>

    val context: Context get() = composeTestRule.activity

    @BeforeTest
    fun baseHiltTestSetup() {
        hiltAndroidRule.inject()
    }

    @AfterTest
    fun baseHiltTestTeardown() {
        appDatabase.close()
    }

    fun runAppTest(
        testBody: suspend TestScope.() -> Unit,
    ): TestResult = runTest {
        updatables.forEach { updatable ->
            backgroundScope.launch {
                updatable.update()
            }
        }
        testBody()
    }
}

private fun createLeakRule(tag: String) =
    if (Build.FINGERPRINT.lowercase() == "robolectric") {
        TestRule { base, _ -> base }
    } else {
        DetectLeaksAfterTestSuccess(tag)
    }
