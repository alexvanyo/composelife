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

package com.alexvanyo.composelife.buildlogic

import org.gradle.api.Project
import org.gradle.api.provider.Provider
import org.gradle.api.services.BuildService
import org.gradle.api.services.BuildServiceParameters

interface HeavyTaskLimitingBuildService : BuildService<BuildServiceParameters.None> {
    companion object {
        fun createKey(): String = "HeavyTaskLimitingBuildService"
    }
}

val Project.heavyTaskLimitingBuildService: Provider<HeavyTaskLimitingBuildService>
    get() = gradle.sharedServices.registerIfAbsent(
        HeavyTaskLimitingBuildService.createKey(),
        HeavyTaskLimitingBuildService::class.java,
    ) {
        maxParallelUsages.set(
            providers.gradleProperty("com.alexvanyo.composelife.maxConcurrentHeavyTasks")
                .map { value -> value.toIntOrNull() },
        )
    }
