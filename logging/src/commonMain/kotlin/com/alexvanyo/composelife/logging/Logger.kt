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

@Suppress("TooManyFunctions")
interface Logger {

    val tag: String

    fun withTag(tag: String): Logger

    fun v(throwable: Throwable? = null, tag: String = this.tag, message: () -> String)

    fun d(throwable: Throwable? = null, tag: String = this.tag, message: () -> String)

    fun i(throwable: Throwable? = null, tag: String = this.tag, message: () -> String)

    fun w(throwable: Throwable? = null, tag: String = this.tag, message: () -> String)

    fun e(throwable: Throwable? = null, tag: String = this.tag, message: () -> String)

    fun a(throwable: Throwable? = null, tag: String = this.tag, message: () -> String)

    fun v(messageString: String, throwable: Throwable? = null, tag: String = this.tag)

    fun d(messageString: String, throwable: Throwable? = null, tag: String = this.tag)

    fun i(messageString: String, throwable: Throwable? = null, tag: String = this.tag)

    fun w(messageString: String, throwable: Throwable? = null, tag: String = this.tag)

    fun e(messageString: String, throwable: Throwable? = null, tag: String = this.tag)

    fun a(messageString: String, throwable: Throwable? = null, tag: String = this.tag)

    companion object
}

@JvmOverloads
fun Logger.Companion.v(tag: String = SingletonSystemLogger.tag, throwable: Throwable? = null, message: () -> String) =
    SingletonSystemLogger.v(tag = tag, throwable = throwable, message = message)

@JvmOverloads
fun Logger.Companion.d(tag: String = SingletonSystemLogger.tag, throwable: Throwable? = null, message: () -> String) =
    SingletonSystemLogger.d(tag = tag, throwable = throwable, message = message)

@JvmOverloads
fun Logger.Companion.i(tag: String = SingletonSystemLogger.tag, throwable: Throwable? = null, message: () -> String) =
    SingletonSystemLogger.i(tag = tag, throwable = throwable, message = message)

@JvmOverloads
fun Logger.Companion.w(tag: String = SingletonSystemLogger.tag, throwable: Throwable? = null, message: () -> String) =
    SingletonSystemLogger.w(tag = tag, throwable = throwable, message = message)

@JvmOverloads
fun Logger.Companion.e(tag: String = SingletonSystemLogger.tag, throwable: Throwable? = null, message: () -> String) =
    SingletonSystemLogger.e(tag = tag, throwable = throwable, message = message)

@JvmOverloads
fun Logger.Companion.a(tag: String = SingletonSystemLogger.tag, throwable: Throwable? = null, message: () -> String) =
    SingletonSystemLogger.a(tag = tag, throwable = throwable, message = message)
