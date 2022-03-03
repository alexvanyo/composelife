package com.alexvanyo.composelife.test

import android.content.Context
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
@RunWith(AndroidJUnit4::class)
abstract class BaseAndroidTest {

    @get:Rule(order = 0)
    val hiltAndroidRule = HiltAndroidRule(this)

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
        testBody: suspend TestScope.() -> Unit
    ): TestResult = runTest {
        initPreferences()
        testBody()
    }

    private suspend fun initPreferences() {
        preferences.setAlgorithmChoice(AlgorithmType.HashLifeAlgorithm)
        preferences.setCurrentShapeType(CurrentShapeType.RoundRectangle)
        preferences.setRoundRectangleConfig(
            CurrentShape.RoundRectangle(
                sizeFraction = 1f,
                cornerFraction = 0f
            )
        )
    }
}
