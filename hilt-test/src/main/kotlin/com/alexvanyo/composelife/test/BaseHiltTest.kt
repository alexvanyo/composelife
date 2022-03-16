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

@OptIn(ExperimentalCoroutinesApi::class)
@Suppress("UnnecessaryAbstractClass")
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
