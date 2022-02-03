package com.alexvanyo.composelife.preferences

import android.app.Application
import androidx.test.core.app.ApplicationProvider
import org.junit.rules.TemporaryFolder
import org.junit.rules.TestRule
import org.junit.runner.Description
import org.junit.runners.model.Statement

/**
 * A [TestRule] for setting up preferences with a temporary, automatically cleaned-up file.
 *
 * This rule should be applied, and then the [fileProvider] should be bound to Dagger.
 */
class PreferencesRule : TestRule {
    private val temporaryFolder = TemporaryFolder(ApplicationProvider.getApplicationContext<Application>().cacheDir)

    override fun apply(base: Statement, description: Description): Statement =
        temporaryFolder.apply(base, description)

    /**
     * The [FileProvider] to bind to Dagger for storing the preferences in a temporary way.
     */
    val fileProvider: FileProvider = FileProvider { temporaryFolder.newFile("preferences.pb.tmp") }
}
