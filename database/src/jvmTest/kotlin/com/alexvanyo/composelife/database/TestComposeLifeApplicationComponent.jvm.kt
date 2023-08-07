package com.alexvanyo.composelife.database

import com.alexvanyo.composelife.database.di.TestDatabaseComponent
import com.alexvanyo.composelife.dispatchers.di.TestDispatchersComponent
import com.alexvanyo.composelife.scopes.ApplicationComponent
import me.tatarka.inject.annotations.Component

@Component
actual abstract class TestComposeLifeApplicationComponent :
    ApplicationComponent(),
    TestDatabaseComponent,
    TestDispatchersComponent {
    actual companion object
}

actual fun TestComposeLifeApplicationComponent.Companion.create(): TestComposeLifeApplicationComponent =
    TestComposeLifeApplicationComponent::class.create()
