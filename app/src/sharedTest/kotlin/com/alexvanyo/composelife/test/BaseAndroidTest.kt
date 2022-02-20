package com.alexvanyo.composelife.test

import android.content.Context
import androidx.test.ext.junit.runners.AndroidJUnit4
import com.alexvanyo.composelife.preferences.PreferencesRule
import dagger.hilt.android.qualifiers.ApplicationContext
import dagger.hilt.android.testing.HiltAndroidRule
import kotlinx.coroutines.ExperimentalCoroutinesApi
import org.junit.Before
import org.junit.Rule
import org.junit.runner.RunWith
import javax.inject.Inject

@OptIn(ExperimentalCoroutinesApi::class)
@RunWith(AndroidJUnit4::class)
abstract class BaseAndroidTest {

    @get:Rule
    val preferencesRule = PreferencesRule()

    @get:Rule(order = 0)
    val hiltAndroidRule = HiltAndroidRule(this)

    @Inject
    @ApplicationContext
    lateinit var context: Context

    @Before
    fun setup() {
        hiltAndroidRule.inject()
    }
}
