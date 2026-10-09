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

import com.alexvanyo.composelife.buildlogic.ConventionPlugin
import com.alexvanyo.composelife.buildlogic.HeavyTaskLimitingBuildService
import com.alexvanyo.composelife.buildlogic.configureKotlin
import com.alexvanyo.composelife.buildlogic.heavyTaskLimitingBuildService
import org.gradle.api.provider.Provider
import org.gradle.api.tasks.TaskContainer
import org.gradle.api.tasks.testing.AbstractTestTask
import org.jetbrains.kotlin.gradle.targets.js.testing.KotlinJsTest
import org.jetbrains.kotlin.gradle.targets.js.testing.karma.KotlinKarma
import java.io.File

class KotlinMultiplatformConventionPlugin :
    ConventionPlugin({
        pluginManager.apply("org.jetbrains.kotlin.multiplatform")

        configureKotlin()

        tasks.withType(AbstractTestTask::class.java).configureEach {
            usesService(heavyTaskLimitingBuildService)
        }

        val karmaConfigDir = isolated.rootProject.projectDirectory.dir("config/karma").asFile
        configureKotlinJsTest(
            tasks = tasks,
            heavyTaskLimitingBuildService = heavyTaskLimitingBuildService,
            karmaConfigDir = karmaConfigDir,
        )
    })

private fun configureKotlinJsTest(
    tasks: TaskContainer,
    heavyTaskLimitingBuildService: Provider<HeavyTaskLimitingBuildService>,
    karmaConfigDir: File,
) {
    tasks.withType(KotlinJsTest::class.java).configureEach {
        usesService(heavyTaskLimitingBuildService)
        onTestFrameworkSet {
            if (this is KotlinKarma) {
                useConfigDirectory(karmaConfigDir)
            }
        }
    }
}
