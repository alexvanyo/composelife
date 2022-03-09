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

package com.alexvanyo.composelife.preferences

import android.app.Application
import androidx.test.core.app.ApplicationProvider
import androidx.test.ext.junit.runners.AndroidJUnit4
import dagger.hilt.android.testing.BindValue
import dagger.hilt.android.testing.HiltAndroidRule
import dagger.hilt.android.testing.HiltAndroidTest
import org.junit.Before
import org.junit.Rule
import org.junit.Test
import org.junit.runner.RunWith
import java.io.File
import javax.inject.Inject
import kotlin.test.assertTrue

@HiltAndroidTest
@RunWith(AndroidJUnit4::class)
class TestPreferencesDataStoreTests {

    private val context = ApplicationProvider.getApplicationContext<Application>()

    @get:Rule
    val preferencesRule = PreferencesRule()

    @get:Rule
    val hiltAndroidRule = HiltAndroidRule(this)

    @BindValue
    val fileProvider: FileProvider = preferencesRule.fileProvider

    @Inject
    @PreferencesProtoFile
    lateinit var file: File

    @Before
    fun setup() {
        hiltAndroidRule.inject()
    }

    @Test
    fun file_is_in_cache_dir() {
        assertTrue(context.cacheDir.walkBottomUp().contains(file))
    }

    @Test
    fun file_is_suffixed_with_tmp() {
        assertTrue(file.name.endsWith(".tmp"))
    }
}
