package com.alexvanyo.composelife.preferences

import android.app.Application
import androidx.test.core.app.ApplicationProvider
import androidx.test.ext.junit.runners.AndroidJUnit4
import dagger.hilt.android.testing.HiltAndroidRule
import dagger.hilt.android.testing.HiltAndroidTest
import org.junit.Assert.assertTrue
import org.junit.Before
import org.junit.Rule
import org.junit.Test
import org.junit.runner.RunWith
import java.io.File
import javax.inject.Inject

@HiltAndroidTest
@RunWith(AndroidJUnit4::class)
class TestPreferencesDataStoreTests {
    @get:Rule
    val hiltAndroidRule = HiltAndroidRule(this)

    private val context = ApplicationProvider.getApplicationContext<Application>()

    @Inject
    @PreferencesProto
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
