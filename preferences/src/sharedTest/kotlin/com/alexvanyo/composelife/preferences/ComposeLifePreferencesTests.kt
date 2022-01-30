package com.alexvanyo.composelife.preferences

import androidx.test.ext.junit.runners.AndroidJUnit4
import app.cash.turbine.test
import com.alexvanyo.composelife.preferences.proto.Algorithm
import dagger.hilt.android.testing.HiltAndroidRule
import dagger.hilt.android.testing.HiltAndroidTest
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.runBlocking
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
    val hiltAndroidRule = HiltAndroidRule(this)

    @Inject
    lateinit var composeLifePreferences: ComposeLifePreferences

    @Before
    fun setup() {
        hiltAndroidRule.inject()
    }

    // TODO: Replace with runTest
    @Test
    fun default_value_is_unknown() = runBlocking {
        composeLifePreferences.algorithmChoice.test {
            assertEquals(Algorithm.UNKNOWN, awaitItem())

            cancel()
        }
    }
}
