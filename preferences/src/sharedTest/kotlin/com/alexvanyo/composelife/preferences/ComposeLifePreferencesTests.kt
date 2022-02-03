package com.alexvanyo.composelife.preferences

import androidx.test.ext.junit.runners.AndroidJUnit4
import app.cash.turbine.test
import com.alexvanyo.composelife.preferences.proto.Algorithm
import dagger.hilt.android.testing.BindValue
import dagger.hilt.android.testing.HiltAndroidRule
import dagger.hilt.android.testing.HiltAndroidTest
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.test.TestDispatcher
import kotlinx.coroutines.test.resetMain
import kotlinx.coroutines.test.runTest
import kotlinx.coroutines.test.setMain
import org.junit.After
import org.junit.Assert.assertEquals
import org.junit.Before
import org.junit.Rule
import org.junit.Test
import org.junit.runner.RunWith
import javax.inject.Inject

@OptIn(ExperimentalCoroutinesApi::class)
@HiltAndroidTest
@RunWith(AndroidJUnit4::class)
class ComposeLifePreferencesTests {

    @get:Rule
    val preferencesRule = PreferencesRule()
    
    @get:Rule
    val hiltAndroidRule = HiltAndroidRule(this)

    @BindValue
    val fileProvider = preferencesRule.fileProvider

    @Inject
    lateinit var composeLifePreferences: ComposeLifePreferences

    @Inject
    lateinit var testDispatcher: TestDispatcher

    @Before
    fun setup() {
        hiltAndroidRule.inject()
        Dispatchers.setMain(testDispatcher)
    }

    @After
    fun teardown() {
        Dispatchers.resetMain()
    }

    @Test
    fun default_value_is_unknown() = runTest {
        composeLifePreferences.algorithmChoice.test {
            assertEquals(Algorithm.UNKNOWN, awaitItem())

            cancel()
        }
    }

    @Test
    fun setting_value_updates_value() = runTest {
        composeLifePreferences.algorithmChoice.test {
            assertEquals(Algorithm.UNKNOWN, awaitItem())

            composeLifePreferences.setAlgorithmChoice(Algorithm.HASHLIFE)

            assertEquals(Algorithm.HASHLIFE, awaitItem())

            cancel()
        }
    }
}
