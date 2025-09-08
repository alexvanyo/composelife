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

package com.alexvanyo.composelife.strictmode

import android.app.Application
import android.content.pm.ApplicationInfo
import android.os.Build
import android.os.StrictMode
import com.alexvanyo.composelife.logging.Logger
import com.alexvanyo.composelife.logging.e

fun Application.initStrictModeIfNeeded() {
    if (isDebuggable) {
        initStrictMode()
    }
}

private fun Application.initStrictMode() {
    initStrictModeThreadPolicy()
    initStrictModeVmPolicy()
}

private fun Application.initStrictModeThreadPolicy() {
    StrictMode.setThreadPolicy(
        StrictMode.ThreadPolicy.Builder()
            .apply {
                detectAll()
                if (Build.VERSION.SDK_INT >= 28) {
                    penaltyListener(
                        this@initStrictModeThreadPolicy.mainExecutor,
                    ) {
                        val stackTraceAsString = it.stackTraceToString()
                        if (strictModeAllowlist.none(stackTraceAsString::contains)) {
                            Logger.e("StrictMode", it) { "StrictMode ThreadPolicy violation" }
                            @Suppress("TooGenericExceptionThrown")
                            throw RuntimeException("StrictMode ThreadPolicy violation", it)
                        }
                    }
                } else {
                    penaltyLog()
                    penaltyDeath()
                }
            }
            .build(),
    )
}

private fun Application.initStrictModeVmPolicy() {
    StrictMode.setVmPolicy(
        StrictMode.VmPolicy.Builder()
            .apply {
                detectAll()
                if (Build.VERSION.SDK_INT >= 28) {
                    penaltyListener(
                        this@initStrictModeVmPolicy.mainExecutor,
                    ) {
                        val stackTraceAsString = it.stackTraceToString()
                        if (strictModeAllowlist.none(stackTraceAsString::contains)) {
                            Logger.e("StrictMode", it) { "StrictMode VmPolicy violation" }
                            @Suppress("TooGenericExceptionThrown")
                            throw RuntimeException("StrictMode VmPolicy violation", it)
                        }
                    }
                } else {
                    penaltyLog()
                    penaltyDeath()
                }
            }
            .build(),
    )
}

private val strictModeAllowlist: List<String> = listOf(
    "android.app.IdsController.doIds", // Samsung
    "com.mediatek.boostfwk",           // MediaTek Boost framework
    "com.mediatek.scnmodule",          // MediaTek
)

private val Application.isDebuggable get() =
    applicationInfo.flags and ApplicationInfo.FLAG_DEBUGGABLE != 0
