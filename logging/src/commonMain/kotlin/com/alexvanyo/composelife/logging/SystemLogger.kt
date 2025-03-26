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

package com.alexvanyo.composelife.logging

import co.touchlab.kermit.LoggerConfig
import co.touchlab.kermit.StaticConfig
import co.touchlab.kermit.platformLogWriter

@Suppress("TooManyFunctions")
internal class SystemLogger(
    private val kermitLoggerConfig: LoggerConfig = StaticConfig(
        logWriterList = listOf(platformLogWriter()),
    ),
    override val tag: String = "ComposeLife",
) : Logger {
    private val kermitLogger = co.touchlab.kermit.Logger(
        config = kermitLoggerConfig,
        tag = tag,
    )

    override fun withTag(tag: String): Logger =
        SystemLogger(kermitLoggerConfig, tag)

    override fun v(throwable: Throwable?, tag: String, message: () -> String) =
        kermitLogger.v(throwable, tag, message)

    override fun d(throwable: Throwable?, tag: String, message: () -> String) =
        kermitLogger.d(throwable, tag, message)

    override fun i(throwable: Throwable?, tag: String, message: () -> String) =
        kermitLogger.i(throwable, tag, message)

    override fun w(throwable: Throwable?, tag: String, message: () -> String) =
        kermitLogger.w(throwable, tag, message)

    override fun e(throwable: Throwable?, tag: String, message: () -> String) =
        kermitLogger.e(throwable, tag, message)

    override fun a(throwable: Throwable?, tag: String, message: () -> String) =
        kermitLogger.a(throwable, tag, message)

    override fun v(messageString: String, throwable: Throwable?, tag: String) =
        kermitLogger.v(messageString, throwable, tag)

    override fun d(messageString: String, throwable: Throwable?, tag: String) =
        kermitLogger.d(messageString, throwable, tag)

    override fun i(messageString: String, throwable: Throwable?, tag: String) =
        kermitLogger.i(messageString, throwable, tag)

    override fun w(messageString: String, throwable: Throwable?, tag: String) =
        kermitLogger.w(messageString, throwable, tag)

    override fun e(messageString: String, throwable: Throwable?, tag: String) =
        kermitLogger.e(messageString, throwable, tag)

    override fun a(messageString: String, throwable: Throwable?, tag: String) =
        kermitLogger.a(messageString, throwable, tag)
}

internal val SingletonSystemLogger = SystemLogger()
