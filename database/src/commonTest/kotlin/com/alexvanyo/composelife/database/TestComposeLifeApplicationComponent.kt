package com.alexvanyo.composelife.database

import com.alexvanyo.composelife.database.di.TestDatabaseComponent
import com.alexvanyo.composelife.dispatchers.di.TestDispatchersComponent
import com.alexvanyo.composelife.scopes.ApplicationComponent

expect abstract class TestComposeLifeApplicationComponent :
    ApplicationComponent,
    TestDatabaseComponent,
    TestDispatchersComponent {
    companion object
}

expect fun TestComposeLifeApplicationComponent.Companion.create(): TestComposeLifeApplicationComponent
