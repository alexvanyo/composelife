package com.alexvanyo.composelife.preferences

import androidx.test.ext.junit.runners.AndroidJUnit4
import com.alexvanyo.composelife.dispatchers.di.TestDispatcherModule
import com.alexvanyo.composelife.resourcestate.ResourceState
import dagger.hilt.android.testing.BindValue
import dagger.hilt.android.testing.HiltAndroidRule
import dagger.hilt.android.testing.HiltAndroidTest
import dagger.hilt.android.testing.UninstallModules
import kotlinx.coroutines.Dispatchers
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.test.StandardTestDispatcher
import kotlinx.coroutines.test.advanceUntilIdle
import kotlinx.coroutines.test.resetMain
import kotlinx.coroutines.test.runTest
import kotlinx.coroutines.test.setMain
import org.junit.After
import org.junit.Before
import org.junit.Rule
import org.junit.Test
import org.junit.runner.RunWith
import javax.inject.Inject
import kotlin.test.assertEquals

@OptIn(ExperimentalCoroutinesApi::class)
@HiltAndroidTest
@UninstallModules(TestDispatcherModule::class)
@RunWith(AndroidJUnit4::class)
class ComposeLifePreferencesTests {

    @get:Rule
    val preferencesRule = PreferencesRule()

    @get:Rule
    val hiltAndroidRule = HiltAndroidRule(this)

    @BindValue
    val fileProvider = preferencesRule.fileProvider

    @Inject
    lateinit var composeLifePreferences: DefaultComposeLifePreferences

    @BindValue
    val testDispatcher = StandardTestDispatcher().also(Dispatchers::setMain)

    @Before
    fun setup() {
        hiltAndroidRule.inject()
    }

    @After
    fun teardown() {
        Dispatchers.resetMain()
    }

    @Test
    fun default_value_is_hashlife() = runTest {
        assertEquals(ResourceState.Loading, composeLifePreferences.algorithmChoiceState)

        advanceUntilIdle()

        assertEquals(
            ResourceState.Success(AlgorithmType.HashLifeAlgorithm),
            composeLifePreferences.algorithmChoiceState
        )
    }

    @Test
    fun setting_algorithm_choice_updates_value() = runTest {
        assertEquals(ResourceState.Loading, composeLifePreferences.algorithmChoiceState)

        advanceUntilIdle()

        assertEquals(
            ResourceState.Success(AlgorithmType.HashLifeAlgorithm),
            composeLifePreferences.algorithmChoiceState
        )

        composeLifePreferences.setAlgorithmChoice(AlgorithmType.NaiveAlgorithm)
        advanceUntilIdle()

        assertEquals(ResourceState.Success(AlgorithmType.NaiveAlgorithm), composeLifePreferences.algorithmChoiceState)
    }
}
