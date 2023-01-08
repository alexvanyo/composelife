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

package com.alexvanyo.composelife.donotkeepprocess

import androidx.compose.runtime.snapshotFlow
import androidx.lifecycle.DefaultLifecycleObserver
import androidx.lifecycle.LifecycleOwner
import com.alexvanyo.composelife.preferences.ComposeLifePreferences
import com.alexvanyo.composelife.processlifecycle.ProcessLifecycle
import com.alexvanyo.composelife.resourcestate.ResourceState
import com.alexvanyo.composelife.updatable.Updatable
import kotlinx.coroutines.awaitCancellation
import kotlinx.coroutines.flow.collectLatest
import javax.inject.Inject
import kotlin.system.exitProcess

class DoNotKeepProcess @Inject constructor(
    @ProcessLifecycle private val lifecycleOwner: LifecycleOwner,
    private val composeLifePreferences: ComposeLifePreferences,
) : Updatable {
    override suspend fun update(): Nothing {
        snapshotFlow {
            when (val doNotKeepProcessState = composeLifePreferences.doNotKeepProcessState) {
                is ResourceState.Failure,
                ResourceState.Loading,
                -> false
                is ResourceState.Success -> doNotKeepProcessState.value
            }
        }.collectLatest { doNotKeepProcess ->
            if (doNotKeepProcess) {
                val observer = object : DefaultLifecycleObserver {
                    override fun onStop(owner: LifecycleOwner) = exitProcess(0)
                }
                lifecycleOwner.lifecycle.addObserver(observer)
                try {
                    awaitCancellation()
                } finally {
                    lifecycleOwner.lifecycle.removeObserver(observer)
                }
            }
        }

        error("snapshotFlow can not complete normally")
    }
}
