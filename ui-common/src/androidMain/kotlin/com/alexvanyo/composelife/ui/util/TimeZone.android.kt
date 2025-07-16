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
import androidx.compose.runtime.Composable
import androidx.compose.runtime.LaunchedEffect
import androidx.compose.runtime.getValue
import androidx.compose.runtime.mutableStateOf
import androidx.compose.runtime.setValue
import androidx.compose.ui.platform.LocalContext
import androidx.core.content.ContextCompat
import androidx.lifecycle.Lifecycle
import androidx.lifecycle.compose.LocalLifecycleOwner
import androidx.lifecycle.repeatOnLifecycle
import kotlinx.coroutines.awaitCancellation
import kotlinx.datetime.TimeZone
import java.util.concurrent.atomic.AtomicInteger

@Composable
actual fun currentTimeZone(lifecycleState: Lifecycle.State): TimeZone {
    val applicationContext = LocalContext.current.applicationContext
    val lifecycleOwner = LocalLifecycleOwner.current
    LaunchedEffect(applicationContext, lifecycleOwner) {
        lifecycleOwner.repeatOnLifecycle(lifecycleState) {
            TimeZoneBroadcastReceiver.update(applicationContext)
        }
    }
    // Update the time zone with the current one in case it changed while the process has been alive, but not while
    // listening for updates. This avoids one frame where the time zone is incorrect if this comes into composition
    // in that state, even though the LaunchedEffect would update it quickly after
    TimeZoneBroadcastReceiver.timeZone = TimeZone.currentSystemDefault()
    return TimeZoneBroadcastReceiver.timeZone
}

/**
 * A global singleton [BroadcastReceiver] to listen for time zone changes.
 *
 * The use of a singleton avoids registering many [BroadcastReceiver] if many pieces of UI all listen for the current
 * time zone.
 */
private object TimeZoneBroadcastReceiver : BroadcastReceiver() {
    var timeZone by mutableStateOf(TimeZone.currentSystemDefault())

    private val count = AtomicInteger(0)

    override fun onReceive(context: Context, intent: Intent) {
        timeZone = TimeZone.currentSystemDefault()
    }

    suspend fun update(context: Context): Nothing {
        timeZone = TimeZone.currentSystemDefault()

        val applicationContext = context.applicationContext
        try {
            if (count.andIncrement == 0) {
                // If the increment increased from 0, register the receiver
                applicationContext.registerReceiverCompat(
                    receiver = this,
                    filter = IntentFilter(Intent.ACTION_TIMEZONE_CHANGED),
                    flags = ContextCompat.RECEIVER_NOT_EXPORTED,
                )
            }
            awaitCancellation()
        } finally {
            if (count.decrementAndGet() == 0) {
                // If the increment decreased to 0, unregister the receiver
                // There should be exactly one application context, so it is fine if the context this function
                // was called with was different than the one that registered the receiver
                applicationContext.unregisterReceiver(this)
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
