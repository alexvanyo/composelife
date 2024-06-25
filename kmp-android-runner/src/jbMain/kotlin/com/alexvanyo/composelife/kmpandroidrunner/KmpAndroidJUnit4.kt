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
package com.alexvanyo.composelife.kmpandroidrunner

import org.junit.runner.Description
import org.junit.runner.Runner
import org.junit.runner.notification.RunNotifier

/**
 * A [Runner] to be used with multiplatform Compose tests.
 *
 * Internally, this delegates to a platform specific runner.
 */
class KmpAndroidJUnit4(
    klass: Class<*>,
) : Runner() {
    private val delegateRunner = createRunner(klass)
    override fun getDescription(): Description = delegateRunner.description
    override fun run(notifier: RunNotifier?) = delegateRunner.run(notifier)
}

internal expect fun createRunner(klass: Class<*>): Runner
