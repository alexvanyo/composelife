/*
 * Copyright 2025 The Android Open Source Project
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

package com.alexvanyo.composelife

import androidx.activity.ComponentActivity
import androidx.compose.runtime.CancellationHandle
import androidx.compose.runtime.CompositionContext
import androidx.compose.runtime.ControlledRetainScope
import androidx.compose.runtime.RetainScope
import androidx.lifecycle.DefaultLifecycleObserver
import androidx.lifecycle.LifecycleOwner
import androidx.lifecycle.ViewModel

/**
 * TODO: Replace when official support is added for [RetainScope] for [ComponentActivity].
 */
internal class ActivityRetainScopeOwner : ViewModel() {

    private var isInstalledInActivity = false

    private val controlledRetainScope = ControlledRetainScope()
    val retainScope: RetainScope
        get() = controlledRetainScope

    private var endRetainCancellationHandle: CancellationHandle? = null
        set(value) {
            field?.cancel()
            field = value
        }

    fun installIn(activity: ComponentActivity, compositionContext: CompositionContext) {
        if (isInstalledInActivity) return
        isInstalledInActivity = true

        activity.lifecycle.addObserver(
            object : DefaultLifecycleObserver {
                override fun onResume(owner: LifecycleOwner) {
                    if (controlledRetainScope.isKeepingExitedValues) {
                        endRetainCancellationHandle =
                            compositionContext.scheduleFrameEndCallback {
                                controlledRetainScope.stopKeepingExitedValues()
                            }
                    }
                }

                override fun onStop(owner: LifecycleOwner) {
                    endRetainCancellationHandle = null
                    if (activity.isChangingConfigurations) {
                        controlledRetainScope.startKeepingExitedValues()
                    }
                }

                override fun onDestroy(owner: LifecycleOwner) {
                    isInstalledInActivity = false
                    owner.lifecycle.removeObserver(this)
                    endRetainCancellationHandle = null
                }
            },
        )
    }

    override fun onCleared() {
        endRetainCancellationHandle?.cancel()
        if (controlledRetainScope.isKeepingExitedValues) {
            controlledRetainScope.stopKeepingExitedValues()
        }
    }
}
