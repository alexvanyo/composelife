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

package com.alexvanyo.composelife.ui.util

import android.content.BroadcastReceiver
import android.content.Context
import android.content.Intent
import android.content.IntentFilter
import android.os.Build
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.core.content.ContextCompat
import com.alexvanyo.composelife.scopes.ApplicationContext
import com.alexvanyo.composelife.updatable.Updatable
import dev.zacsweers.metro.AppScope
import dev.zacsweers.metro.ContributesBinding
import dev.zacsweers.metro.Inject
import dev.zacsweers.metro.SingleIn
import dev.zacsweers.metro.binding
import kotlinx.coroutines.awaitCancellation
import kotlinx.datetime.TimeZone
import java.util.concurrent.atomic.AtomicInteger

/**
 * A global singleton [BroadcastReceiver] to listen for time zone changes.
 *
 * The use of a singleton avoids registering many [BroadcastReceiver] if many pieces of UI all listen for the current
 * time zone.
 */
@SingleIn(AppScope::class)
@ContributesBinding(AppScope::class, binding<TimeZoneHolder>())
@Inject
class AndroidTimeZoneHolder(
    @param:ApplicationContext private val context: Context,
) : BroadcastReceiver(), TimeZoneHolder, Updatable {
    private var _timeZone by mutableStateOf(TimeZone.currentSystemDefault())

    override val timeZone: TimeZone
        get() {
            val currentTimeZone = TimeZone.currentSystemDefault()
            // Update the time zone with the current one in case it changed while the process has been alive, but not
            // while listening for updates. This avoids one frame where the time zone is incorrect if this comes into
            // composition in that state, even though the LaunchedEffect would update it quickly after
            if (_timeZone != currentTimeZone) {
                _timeZone = currentTimeZone
            }
            return _timeZone
        }

    private val count = AtomicInteger(0)

    override fun onReceive(context: Context, intent: Intent) {
        _timeZone = TimeZone.currentSystemDefault()
    }

    override suspend fun update(): Nothing {
        _timeZone = TimeZone.currentSystemDefault()

        try {
            if (count.andIncrement == 0) {
                // If the increment increased from 0, register the receiver
                context.registerReceiverCompat(
                    receiver = this,
                    filter = IntentFilter(Intent.ACTION_TIMEZONE_CHANGED),
                    flags = ContextCompat.RECEIVER_NOT_EXPORTED,
                )
            }
            awaitCancellation()
        } finally {
            if (count.decrementAndGet() == 0) {
                // If the increment decreased to 0, unregister the receiver
                context.unregisterReceiver(this)
            }
        }
    }
}

private fun Context.registerReceiverCompat(
    receiver: BroadcastReceiver,
    filter: IntentFilter,
    flags: Int,
) {
    if (Build.FINGERPRINT.lowercase() == "robolectric") {
        if (Build.VERSION.SDK_INT >= 33) {
            ContextCompat.registerReceiver(
                this,
                receiver,
                IntentFilter(Intent.ACTION_TIMEZONE_CHANGED),
                ContextCompat.RECEIVER_NOT_EXPORTED,
            )
        } else if (Build.VERSION.SDK_INT >= 26) {
            registerReceiver(
                receiver,
                filter,
                if (flags and ContextCompat.RECEIVER_VISIBLE_TO_INSTANT_APPS != 0) {
                    Context.RECEIVER_VISIBLE_TO_INSTANT_APPS
                } else {
                    0
                },
            )
        } else {
            @Suppress("UnspecifiedRegisterReceiverFlag")
            registerReceiver(
                receiver,
                filter,
            )
        }
    } else {
        ContextCompat.registerReceiver(
            this,
            receiver,
            IntentFilter(Intent.ACTION_TIMEZONE_CHANGED),
            ContextCompat.RECEIVER_NOT_EXPORTED,
        )
    }
}
