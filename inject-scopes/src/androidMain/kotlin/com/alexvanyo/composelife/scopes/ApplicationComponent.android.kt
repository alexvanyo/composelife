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

package com.alexvanyo.composelife.scopes

import android.app.Application
import android.content.Context
import com.alexvanyo.composelife.entrypoint.EntryPointProvider
import me.tatarka.inject.annotations.Provides
import software.amazon.lastmile.kotlin.inject.anvil.AppScope
import software.amazon.lastmile.kotlin.inject.anvil.SingleIn

@Suppress("UnnecessaryAbstractClass")
@SingleIn(AppScope::class)
actual abstract class ApplicationComponent(
    @get:Provides val application: Application,
) : EntryPointProvider<AppScope> {
    @Provides
    @ApplicationContext
    fun bindApplication(application: Application): Context = application
}
