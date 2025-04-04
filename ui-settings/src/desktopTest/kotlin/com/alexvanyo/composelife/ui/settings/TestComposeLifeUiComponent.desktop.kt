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

package com.alexvanyo.composelife.ui.settings

import com.alexvanyo.composelife.entrypoint.EntryPointProvider
import com.alexvanyo.composelife.scopes.UiComponent
import com.alexvanyo.composelife.scopes.UiComponentArguments
import com.alexvanyo.composelife.scopes.UiScope
import software.amazon.lastmile.kotlin.inject.anvil.AppScope
import software.amazon.lastmile.kotlin.inject.anvil.ContributesSubcomponent
import software.amazon.lastmile.kotlin.inject.anvil.SingleIn
import kotlin.reflect.KClass

@ContributesSubcomponent(UiScope::class)
@SingleIn(UiScope::class)
actual interface TestComposeLifeUiComponent : UiComponent {
    @ContributesSubcomponent.Factory(AppScope::class)
    actual interface Factory {
        fun createTestComponent(): TestComposeLifeUiComponent
    }

    actual companion object
}

actual fun TestComposeLifeUiComponent.Companion.createComponent(
    applicationComponent: TestComposeLifeApplicationComponent,
    uiComponentArguments: UiComponentArguments,
): TestComposeLifeUiComponent =
    applicationComponent.getEntryPoint<TestComposeLifeApplicationEntryPoint>().uiComponentFactory.createTestComponent()

actual inline fun <reified T : TestComposeLifeUiEntryPoint> EntryPointProvider<UiScope>.kmpGetEntryPoint(
    unused: KClass<T>,
): TestComposeLifeUiEntryPoint = getEntryPoint<TestComposeLifeUiEntryPoint>()
