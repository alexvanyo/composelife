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
import androidx.activity.ComponentActivity
import androidx.compose.ui.test.junit4.createAndroidComposeRule
import androidx.test.ext.junit.runners.AndroidJUnit4
import com.alexvanyo.composelife.preferences.AlgorithmType
import com.alexvanyo.composelife.preferences.CurrentShape
import com.alexvanyo.composelife.preferences.CurrentShapeType
import com.alexvanyo.composelife.preferences.TestComposeLifePreferences
import dagger.hilt.android.qualifiers.ApplicationContext
import dagger.hilt.android.testing.HiltAndroidRule
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.test.TestResult
import kotlinx.coroutines.test.TestScope
import kotlinx.coroutines.test.runTest
import org.junit.Before
import org.junit.Rule
import org.junit.runner.RunWith
import javax.inject.Inject

@Suppress("UnnecessaryAbstractClass")
@OptIn(ExperimentalCoroutinesApi::class)
@RunWith(AndroidJUnit4::class)
abstract class BaseHiltTest<T : ComponentActivity>(clazz: Class<T>) {

    @get:Rule(order = 0)
    val hiltAndroidRule = HiltAndroidRule(this)

    @get:Rule(order = 1)
    val composeTestRule = createAndroidComposeRule(clazz)

    @Inject
    lateinit var preferences: TestComposeLifePreferences

    @Inject
    @ApplicationContext
    lateinit var context: Context

    @Before
    fun setup() {
        hiltAndroidRule.inject()
    }

    fun runAppTest(
        preferencesInitializer: suspend TestComposeLifePreferences.() -> Unit = {
            setAlgorithmChoice(AlgorithmType.HashLifeAlgorithm)
            setCurrentShapeType(CurrentShapeType.RoundRectangle)
            setRoundRectangleConfig(
                CurrentShape.RoundRectangle(
                    sizeFraction = 1f,
                    cornerFraction = 0f
                )
            )
        },
        testBody: suspend TestScope.() -> Unit
    ): TestResult = runTest {
        preferencesInitializer(preferences)
        testBody()
    }
}
