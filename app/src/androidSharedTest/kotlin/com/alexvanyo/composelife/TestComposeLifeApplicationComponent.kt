/*
 * Copyright 2023 The Android Open Source Project
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
@file:Suppress("MatchingDeclarationName")

package com.alexvanyo.composelife

import android.app.Application
import com.alexvanyo.composelife.dispatchers.di.TestDispatcherModule
import com.alexvanyo.composelife.entrypoint.EntryPoint
import com.alexvanyo.composelife.entrypoint.EntryPointProvider
import com.alexvanyo.composelife.preferences.di.PreferencesModule
import com.alexvanyo.composelife.scopes.ApplicationComponent
import com.alexvanyo.composelife.updatable.di.UpdatableModule
import software.amazon.lastmile.kotlin.inject.anvil.AppScope
import software.amazon.lastmile.kotlin.inject.anvil.MergeComponent
import software.amazon.lastmile.kotlin.inject.anvil.SingleIn
import kotlin.reflect.KClass

@MergeComponent(AppScope::class)
@SingleIn(AppScope::class)
abstract class TestComposeLifeApplicationComponent(
    application: Application,
) : ApplicationComponent(application) {
    companion object
}

expect fun TestComposeLifeApplicationComponent.Companion.createComponent(): TestComposeLifeApplicationComponent

@EntryPoint(AppScope::class)
interface TestComposeLifeApplicationEntryPoint :
    UpdatableModule,
    TestDispatcherModule,
    PreferencesModule {
    val uiComponentFactory: TestComposeLifeUiComponent.Factory
}

expect inline fun <reified T : TestComposeLifeApplicationEntryPoint> EntryPointProvider<AppScope>.kmpGetEntryPoint(
    unused: KClass<T> = T::class,
): TestComposeLifeApplicationEntryPoint
