/*
 * Copyright 2022 The Android Open Source Project
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

package com.alexvanyo.composelife.wear

import android.app.Application
import android.content.pm.ApplicationInfo
import android.os.StrictMode
import androidx.lifecycle.Lifecycle
import androidx.lifecycle.lifecycleScope
import androidx.lifecycle.repeatOnLifecycle
import com.alexvanyo.composelife.scopes.ApplicationComponentOwner
import com.alexvanyo.composelife.scopes.UiComponentArguments
import kotlinx.coroutines.launch
import kotlinx.coroutines.supervisorScope

class ComposeLifeApplication : Application(), ApplicationComponentOwner {

    override lateinit var applicationComponent: ComposeLifeApplicationComponent

    override val uiComponentFactory: (UiComponentArguments) -> ComposeLifeUiComponent =
        { ComposeLifeUiComponent::class.create(applicationComponent, it.activity) }

    override fun onCreate() {
        super.onCreate()

        if (isDebuggable) {
            StrictMode.setThreadPolicy(
                StrictMode.ThreadPolicy.Builder()
                    .detectAll()
                    .penaltyLog()
                    .penaltyDeath()
                    .build(),
            )
        }

        applicationComponent = ComposeLifeApplicationComponent::class.create(this)

        val processLifecycleOwner = applicationComponent.processLifecycleOwner
        val updatables = applicationComponent.updatables

        // Update all singleton scoped updatables in the process lifecycle scope, when its created.
        // Effectively, this is just a permanently running coroutine scope.
        processLifecycleOwner.lifecycleScope.launch {
            processLifecycleOwner.repeatOnLifecycle(Lifecycle.State.CREATED) {
                supervisorScope {
                    updatables.forEach { updatable ->
                        launch {
                            updatable.update()
                        }
                    }
                }
            }
        }
    }
}

private val Application.isDebuggable get() =
    applicationInfo.flags and ApplicationInfo.FLAG_DEBUGGABLE != 0
