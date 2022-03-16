package com.alexvanyo.composelife.test

import android.app.Application
import android.content.Context
import androidx.test.runner.AndroidJUnitRunner
import dagger.hilt.android.testing.HiltTestApplication

/**
 * An [AndroidJUnitRunner] that creates a [HiltTestApplication] to host Hilt tests.
 *
 * This is used as the instrumentation runner for on-device tests.
 */
@Suppress("unused")
class HiltTestRunner : AndroidJUnitRunner() {
    override fun newApplication(cl: ClassLoader?, className: String?, context: Context?): Application =
        super.newApplication(cl, HiltTestApplication::class.java.name, context)
}
