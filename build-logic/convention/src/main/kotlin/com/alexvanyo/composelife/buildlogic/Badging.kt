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

package com.alexvanyo.composelife.buildlogic

import com.android.build.api.artifact.SingleArtifact
import com.android.build.api.variant.Aapt2
import com.android.build.api.variant.ApplicationAndroidComponentsExtension
import org.gradle.api.DefaultTask
import org.gradle.api.GradleException
import org.gradle.api.Project
import org.gradle.api.file.DirectoryProperty
import org.gradle.api.file.RegularFileProperty
import org.gradle.api.provider.Property
import org.gradle.api.tasks.CacheableTask
import org.gradle.api.tasks.Copy
import org.gradle.api.tasks.Input
import org.gradle.api.tasks.InputFile
import org.gradle.api.tasks.Nested
import org.gradle.api.tasks.OutputDirectory
import org.gradle.api.tasks.OutputFile
import org.gradle.api.tasks.PathSensitive
import org.gradle.api.tasks.PathSensitivity
import org.gradle.api.tasks.TaskAction
import org.gradle.language.base.plugins.LifecycleBasePlugin
import org.gradle.process.ExecOperations
import java.nio.file.Files
import javax.inject.Inject

@CacheableTask
abstract class GenerateBadgingTask : DefaultTask() {

    @get:OutputFile
    abstract val badging: RegularFileProperty

    @get:PathSensitive(PathSensitivity.NONE)
    @get:InputFile
    abstract val apk: RegularFileProperty

    @get:Nested
    abstract val aapt2: Property<Aapt2>

    @get:Inject
    abstract val execOperations: ExecOperations

    @TaskAction
    fun taskAction() {
        execOperations.exec {
            commandLine(
                aapt2.get().executable.get().asFile.absolutePath,
                "dump",
                "badging",
                apk.get().asFile.absolutePath,
            )
            standardOutput = badging.asFile.get().outputStream()
        }
    }
}

@CacheableTask
abstract class CheckBadgingTask : DefaultTask() {

    // In order for the task to be up-to-date when the inputs have not changed,
    // the task must declare an output, even if it's not used. Tasks with no
    // output are always run regardless of whether the inputs changed
    @get:OutputDirectory
    abstract val output: DirectoryProperty

    @get:PathSensitive(PathSensitivity.NONE)
    @get:InputFile
    abstract val goldenBadging: RegularFileProperty

    @get:PathSensitive(PathSensitivity.NONE)
    @get:InputFile
    abstract val generatedBadging: RegularFileProperty

    @get:Input
    abstract val updateBadgingTaskName: Property<String>

    override fun getGroup(): String = LifecycleBasePlugin.VERIFICATION_GROUP

    @TaskAction
    fun taskAction() {
        if (
            Files.mismatch(
                goldenBadging.get().asFile.toPath(),
                generatedBadging.get().asFile.toPath(),
            ) != -1L
        ) {
            throw GradleException(
                "Generated badging is different from golden badging! " +
                    "If this change is intended, run ./gradlew ${updateBadgingTaskName.get()}",
            )
        }
    }
}

fun Project.configureBadgingTasks(
    componentsExtension: ApplicationAndroidComponentsExtension,
) {
    // Registers a callback to be called, when a new variant is configured
    componentsExtension.onVariants { variant ->
        // Registers a new task to verify the app bundle.
        val capitalizedVariantName = variant.name.capitalizeForTaskName()
        val generateBadgingTaskName = "generate${capitalizedVariantName}Badging"
        val generateBadging = tasks.register(generateBadgingTaskName, GenerateBadgingTask::class.java) {
            apk.set(
                variant.artifacts.get(SingleArtifact.APK_FROM_BUNDLE),
            )
            aapt2.set(componentsExtension.sdkComponents.aapt2)

            badging.set(
                project.layout.buildDirectory.file(
                    "outputs/apk_from_bundle/${variant.name}/${variant.name}-badging.txt",
                ),
            )
        }

        val updateBadgingTaskName = "update${capitalizedVariantName}Badging"
        tasks.register(updateBadgingTaskName, Copy::class.java) {
            from(generateBadging.map(GenerateBadgingTask::badging))
            into(project.layout.projectDirectory)
        }

        val checkBadgingTaskName = "check${capitalizedVariantName}Badging"
        tasks.register(checkBadgingTaskName, CheckBadgingTask::class.java) {
            goldenBadging.set(
                project.layout.projectDirectory.file("${variant.name}-badging.txt"),
            )
            generatedBadging.set(
                generateBadging.flatMap(GenerateBadgingTask::badging),
            )
            this.updateBadgingTaskName.set(updateBadgingTaskName)

            output.set(
                project.layout.buildDirectory.dir("intermediates/$checkBadgingTaskName"),
            )
        }
    }
}
