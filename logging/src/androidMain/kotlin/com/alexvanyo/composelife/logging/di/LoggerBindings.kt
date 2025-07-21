/*
 * Copyright 2024 The Android Open Source Project
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

package com.alexvanyo.composelife.logging.di

import android.app.Application
import android.content.pm.ApplicationInfo
import com.alexvanyo.composelife.logging.Logger
import com.alexvanyo.composelife.logging.NoOpLogger
import com.alexvanyo.composelife.logging.SingletonSystemLogger
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.BindingContainer
import dev.zacsweers.metro.ContributesTo
import dev.zacsweers.metro.Provides

@ContributesTo(AppScope::class)
@BindingContainer
interface LoggerBindings {
    companion object {
        @Provides
        fun providesLogger(
            application: Application,
        ): Logger =
            if (application.isDebuggable) {
                SingletonSystemLogger
            } else {
                NoOpLogger
            }
    }
}

private val Application.isDebuggable get() =
    applicationInfo.flags and ApplicationInfo.FLAG_DEBUGGABLE != 0
