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

package com.alexvanyo.composelife.appcompatsync

import android.app.Activity
import android.app.Application
import android.content.res.Configuration
import androidx.appcompat.app.AppCompatActivity
import androidx.compose.runtime.snapshots.Snapshot
import androidx.test.core.app.ActivityScenario
import androidx.test.core.app.ApplicationProvider
import androidx.test.ext.junit.runners.AndroidJUnit4
import com.alexvanyo.composelife.preferences.DarkThemeConfig
import com.alexvanyo.composelife.preferences.TestComposeLifePreferences
import com.alexvanyo.composelife.preferences.setDarkThemeConfig
import kotlinx.coroutines.ExperimentalCoroutinesApi
import kotlinx.coroutines.channels.Channel
import kotlinx.coroutines.launch
import kotlinx.coroutines.test.runCurrent
import kotlinx.coroutines.test.runTest
import org.junit.runner.RunWith
import kotlin.test.Test
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

@OptIn(ExperimentalCoroutinesApi::class)
@RunWith(AndroidJUnit4::class)
class AppCompatSyncTests {

    private val testComposeLifePreferences = TestComposeLifePreferences()

    private val appCompatSync = AppCompatSync(
        composeLifePreferences = testComposeLifePreferences,
        context = ApplicationProvider.getApplicationContext(),
    )

    @Test
    fun initially_setting_to_system_launches_in_system() = runTest {
        val isSystemInDarkTheme =
            ApplicationProvider.getApplicationContext<Application>().resources.configuration.isDarkThemeActive

        testComposeLifePreferences.setDarkThemeConfig(DarkThemeConfig.FollowSystem)
        backgroundScope.launch { appCompatSync.update() }
        Snapshot.sendApplyNotifications()
        runCurrent()

        val scenario = ActivityScenario.launch(AppCompatActivity::class.java)

        assertEquals(
            isSystemInDarkTheme,
            scenario.withActivity {
                resources.configuration.isDarkThemeActive
            },
        )

        scenario.close()
    }

    @Test
    fun initially_setting_to_light_launches_in_light() = runTest {
        testComposeLifePreferences.setDarkThemeConfig(DarkThemeConfig.Light)
        backgroundScope.launch { appCompatSync.update() }
        Snapshot.sendApplyNotifications()
        runCurrent()

        val scenario = ActivityScenario.launch(AppCompatActivity::class.java)

        assertFalse(
            scenario.withActivity {
                resources.configuration.isDarkThemeActive
            },
        )

        scenario.close()
    }

    @Test
    fun initially_setting_to_dark_launches_in_dark() = runTest {
        testComposeLifePreferences.setDarkThemeConfig(DarkThemeConfig.Dark)
        backgroundScope.launch { appCompatSync.update() }
        Snapshot.sendApplyNotifications()
        runCurrent()

        val scenario = ActivityScenario.launch(AppCompatActivity::class.java)

        assertTrue(
            scenario.withActivity {
                resources.configuration.isDarkThemeActive
            },
        )

        scenario.close()
    }

    @Test
    fun setting_follow_system_updates_to_system() = runTest {
        val isSystemInDarkTheme =
            ApplicationProvider.getApplicationContext<Application>().resources.configuration.isDarkThemeActive

        val scenario = ActivityScenario.launch(AppCompatActivity::class.java)

        val configurationChanges = Channel<Configuration>(capacity = Channel.UNLIMITED)
        scenario.onActivity { activity ->
            activity.addOnConfigurationChangedListener {
                configurationChanges.trySend(it)
            }
        }

        val oppositeSystemTheme = if (isSystemInDarkTheme) {
            DarkThemeConfig.Light
        } else {
            DarkThemeConfig.Dark
        }

        testComposeLifePreferences.setDarkThemeConfig(oppositeSystemTheme)
        backgroundScope.launch { appCompatSync.update() }
        Snapshot.sendApplyNotifications()

        assertEquals(!isSystemInDarkTheme, configurationChanges.receive().isDarkThemeActive)

        testComposeLifePreferences.setDarkThemeConfig(DarkThemeConfig.FollowSystem)

        assertEquals(isSystemInDarkTheme, configurationChanges.receive().isDarkThemeActive)

        scenario.close()
    }

    @Test
    fun setting_light_sets_to_light() = runTest {
        testComposeLifePreferences.setDarkThemeConfig(DarkThemeConfig.Dark)
        backgroundScope.launch { appCompatSync.update() }
        Snapshot.sendApplyNotifications()
        runCurrent()

        val scenario = ActivityScenario.launch(AppCompatActivity::class.java)

        val configurationChanges = Channel<Configuration>(capacity = Channel.UNLIMITED)
        scenario.onActivity { activity ->
            activity.addOnConfigurationChangedListener {
                configurationChanges.trySend(it)
            }
        }

        testComposeLifePreferences.setDarkThemeConfig(DarkThemeConfig.Light)

        assertFalse(configurationChanges.receive().isDarkThemeActive)

        scenario.close()
    }

    @Test
    fun setting_dark_sets_to_dark() = runTest {
        testComposeLifePreferences.setDarkThemeConfig(DarkThemeConfig.Light)
        backgroundScope.launch { appCompatSync.update() }
        Snapshot.sendApplyNotifications()
        runCurrent()

        val scenario = ActivityScenario.launch(AppCompatActivity::class.java)

        val configurationChanges = Channel<Configuration>(capacity = Channel.UNLIMITED)
        scenario.onActivity { activity ->
            activity.addOnConfigurationChangedListener {
                configurationChanges.trySend(it)
            }
        }

        testComposeLifePreferences.setDarkThemeConfig(DarkThemeConfig.Dark)

        assertTrue(configurationChanges.receive().isDarkThemeActive)

        scenario.close()
    }
}

private val Configuration.isDarkThemeActive get() =
    uiMode and Configuration.UI_MODE_NIGHT_MASK == Configuration.UI_MODE_NIGHT_YES

private inline fun <reified A : Activity, T : Any> ActivityScenario<A>.withActivity(
    crossinline block: A.() -> T,
): T {
    var result: Result<T>? = null
    onActivity { activity ->
        result = kotlin.runCatching {
            block(activity)
        }
    }
    @Suppress("UnsafeCallOnNullableType")
    return result!!.getOrThrow()
}
