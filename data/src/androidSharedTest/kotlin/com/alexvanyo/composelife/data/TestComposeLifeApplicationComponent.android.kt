package com.alexvanyo.composelife.data

import android.app.Application
import androidx.test.core.app.ApplicationProvider
import com.alexvanyo.composelife.data.di.RepositoryComponent
import com.alexvanyo.composelife.database.di.TestDatabaseComponent
import com.alexvanyo.composelife.dispatchers.di.TestDispatchersComponent
import com.alexvanyo.composelife.scopes.ApplicationComponent
import me.tatarka.inject.annotations.Component

@Component
actual abstract class TestComposeLifeApplicationComponent(
    application: Application,
) : ApplicationComponent(application),
    RepositoryComponent,
    TestDatabaseComponent,
    TestDispatchersComponent {
    actual companion object
}

actual fun TestComposeLifeApplicationComponent.Companion.create(): TestComposeLifeApplicationComponent =
    TestComposeLifeApplicationComponent::class.create(ApplicationProvider.getApplicationContext<Application>())
