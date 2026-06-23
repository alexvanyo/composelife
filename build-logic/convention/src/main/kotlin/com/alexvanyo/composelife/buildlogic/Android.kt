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

@file:Suppress("InternalAgpApiUsage")

package com.alexvanyo.composelife.buildlogic

import com.android.build.api.dsl.CommonExtension
import com.android.build.api.dsl.KotlinMultiplatformAndroidLibraryTarget
import com.android.build.api.variant.KotlinMultiplatformAndroidComponentsExtension
import com.android.build.gradle.internal.lint.AndroidLintAnalysisTask
import com.android.build.gradle.internal.lint.LintModelWriterTask
import com.android.build.gradle.internal.lint.VariantInputs
import com.android.build.gradle.internal.tasks.R8Task
import org.gradle.api.GradleException
import org.gradle.api.JavaVersion
import org.gradle.api.Project
import org.gradle.api.artifacts.VersionCatalogsExtension
import org.gradle.api.file.ConfigurableFileCollection
import org.jetbrains.kotlin.gradle.dsl.JvmTarget
import org.jetbrains.kotlin.gradle.dsl.KotlinMultiplatformExtension
import org.jetbrains.kotlin.gradle.plugin.KotlinSourceSet
import org.jetbrains.kotlin.tooling.core.withClosure
import java.lang.reflect.Field

fun Project.configureAndroid(commonExtension: CommonExtension) {
    val libs = extensions.getByType(VersionCatalogsExtension::class.java).named("libs")

    commonExtension.apply {
        compileSdk = 37

        lint.apply {
            warningsAsErrors = true
            disable.addAll(listOf("GradleDependency", "OldTargetApi", "AndroidGradlePluginVersion"))
            enable.addAll(listOf("UnsupportedChromeOsHardware"))
        }

        defaultConfig.vectorDrawables.useSupportLibrary = true

        buildTypes.getByName("debug") {
            isPseudoLocalesEnabled = true
        }

        compileOptions.apply {
            sourceCompatibility = JavaVersion.VERSION_11
            targetCompatibility = JavaVersion.VERSION_11
            isCoreLibraryDesugaringEnabled = true
        }

        // Workaround for https://github.com/Kotlin/kotlinx.coroutines/blob/master/kotlinx-coroutines-debug/README.md#build-failures-due-to-duplicate-resource-files
        packaging.resources.excludes.addAll(
            listOf(
                "/META-INF/AL2.0",
                "/META-INF/LGPL2.1",
                "/META-INF/LICENSE.md",
                "/META-INF/LICENSE-notice.md",
                "/META-INF/com.google.dagger_dagger.version",
            ),
        )
    }

    configurations.configureEach {
        resolutionStrategy.eachDependency {
            val version = requested.version.orEmpty()
            // Force guava to always use the android version instead of the jre version
            if (requested.group == "com.google.guava" && requested.name == "guava" && version.endsWith("jre")) {
                useVersion(version.removeSuffix("jre") + "android")
            }
        }
    }

    afterEvaluate {
        addSourceSetsForAndroidMultiplatformAfterEvaluate()
    }

    dependencies.add("coreLibraryDesugaring", libs.findLibrary("android.desugarJdkLibs").get())

    // Register R8 minification as heavy tasks
    tasks.withType(R8Task::class.java).configureEach {
        usesService(heavyTaskLimitingBuildService)
    }
}

fun Project.configureAndroid(extension: KotlinMultiplatformAndroidLibraryTarget) {
    val libs = extensions.getByType(VersionCatalogsExtension::class.java).named("libs")

    extension.apply {
        compileSdk = 37

        lint {
            warningsAsErrors = true
            disable.addAll(listOf("GradleDependency", "OldTargetApi", "AndroidGradlePluginVersion"))
            enable.addAll(listOf("UnsupportedChromeOsHardware"))
        }

        enableCoreLibraryDesugaring = true
        androidResources { enable = true }
        compilations.configureEach {
            compileTaskProvider.configure {
                compilerOptions {
                    jvmTarget.set(JvmTarget.JVM_11)
                }
            }
        }

        // Workaround for https://github.com/Kotlin/kotlinx.coroutines/blob/master/kotlinx-coroutines-debug/README.md#build-failures-due-to-duplicate-resource-files
        packaging {
            resources.excludes.addAll(
                listOf(
                    "/META-INF/AL2.0",
                    "/META-INF/LGPL2.1",
                    "/META-INF/LICENSE.md",
                    "/META-INF/LICENSE-notice.md",
                    "/META-INF/com.google.dagger_dagger.version",
                ),
            )
        }
    }

    extensions.configure(KotlinMultiplatformAndroidComponentsExtension::class.java) {
        onVariants { variant ->
            variant.pseudoLocalesEnabled.set(true)
        }
    }

    configurations.configureEach {
        resolutionStrategy.eachDependency {
            val version = requested.version.orEmpty()
            // Force guava to always use the android version instead of the jre version
            if (requested.group == "com.google.guava" && requested.name == "guava" && version.endsWith("jre")) {
                useVersion(version.removeSuffix("jre") + "android")
            }
        }
    }

    afterEvaluate {
        addSourceSetsForAndroidMultiplatformAfterEvaluate()
    }

    dependencies.add("coreLibraryDesugaring", libs.findLibrary("android.desugarJdkLibs").get())
}

// Adapted from https://github.com/androidx/androidx/blob/androidx-main/buildSrc/private/src/main/kotlin/androidx/build/LintConfiguration.kt

/**
 *
 * If the project is using multiplatform targeted to Android, adds source sets directly to lint
 * tasks, which allows it to run against Android multiplatform projects.
 *
 * Lint is not aware of MPP, and MPP doesn't configure Lint. There is no built-in API to adjust
 * the default Lint task's sources, so we use this hack to manually add sources for MPP source
 * sets. In the future, with the new Kotlin Project Model
 * (https://youtrack.jetbrains.com/issue/KT-42572) and an AGP / MPP integration plugin, this will
 * no longer be needed. See also b/195329463.
 */
private fun Project.addSourceSetsForAndroidMultiplatformAfterEvaluate() {
    val multiplatformExtension = extensions.findByType(KotlinMultiplatformExtension::class.java)
    if (multiplatformExtension == null) return
    if (multiplatformExtension.targets.findByName("android") == null) return

    val androidMain = multiplatformExtension.sourceSets.findByName("androidMain")
    if (androidMain == null) {
        throw GradleException("Failed to find source set with name 'androidMain'")
    }

    // Get all the source sets androidMain transitively / directly depends on.
    val dependencySourceSets = androidMain.withClosure(KotlinSourceSet::dependsOn)

    /** Helper function to add the missing sourcesets to this [VariantInputs] */
    fun VariantInputs.addSourceSets() {
        // Each variant has a source provider for the variant (such as debug) and the 'main'
        // variant. The actual files that Lint will run on is both of these providers
        // combined - so we can just add the dependencies to the first we see.
        val sourceProvider = sourceProviders.get().firstOrNull()
        if (sourceProvider != null) {
            dependencySourceSets.forEach { sourceSet ->
                sourceProvider.javaDirectories.withChangesAllowed {
                    from(sourceSet.kotlin.sourceDirectories)
                }
            }
        }
    }

    // Add the new sources to the lint analysis tasks.
    tasks.withType(AndroidLintAnalysisTask::class.java).configureEach {
        variantInputs.addSourceSets()
    }

    // Also configure the model writing task, so that we don't run into mismatches between
    // analyzed sources in one module and a downstream module
    tasks.withType(LintModelWriterTask::class.java).configureEach {
        variantInputs.addSourceSets()
    }
}

/**
 * Lint uses [ConfigurableFileCollection.disallowChanges] during initialization, which prevents
 * modifying the file collection separately (there is no time to configure it before AGP has
 * initialized and disallowed changes). This uses reflection to temporarily allow changes, and
 * apply [block].
 */
@Suppress("NestedBlockDepth", "ReturnCount")
private fun ConfigurableFileCollection.withChangesAllowed(block: ConfigurableFileCollection.() -> Unit) {
    // 1. Try old Gradle versions where disallowChanges was directly on ConfigurableFileCollection
    val directField = findField("disallowChanges")
    if (directField != null) {
        directField.isAccessible = true
        val originalValue = directField.get(this) as Boolean
        directField.set(this, false)
        try {
            block()
        } finally {
            directField.set(this, originalValue)
        }
    } else {
        // 2. Try valueState field
        val valueStateField = findField("valueState") ?: throw NoSuchFieldException("valueState")
        valueStateField.isAccessible = true
        val valueStateObj = valueStateField.get(this)

        // 2a. Try disallowChanges on valueStateObj
        val disallowChangesField = valueStateObj.findField("disallowChanges")
        if (disallowChangesField != null) {
            disallowChangesField.isAccessible = true
            val originalValue = disallowChangesField.get(valueStateObj) as Boolean
            disallowChangesField.set(valueStateObj, false)
            try {
                block()
            } finally {
                disallowChangesField.set(valueStateObj, originalValue)
            }
        } else {
            // 2b. Try flags byte mask on valueStateObj (Gradle 9.5+)
            val flagsField = valueStateObj.findField("flags")
            val maskField = valueStateObj.findField("DISALLOW_CHANGES")
            if (flagsField != null && maskField != null) {
                flagsField.isAccessible = true
                maskField.isAccessible = true
                val mask = (maskField.get(null) as Number).toInt()
                val originalFlags = (flagsField.get(valueStateObj) as Number).toInt()
                flagsField.set(valueStateObj, (originalFlags and mask.inv()).toByte())
                try {
                    block()
                } finally {
                    flagsField.set(valueStateObj, originalFlags.toByte())
                }
            } else {
                throw NoSuchFieldException("Could not find disallowChanges or flags field on valueState")
            }
        }
    }
}

@Suppress("SwallowedException")
private fun Any.findField(name: String): Field? {
    var clazz: Class<*>? = this::class.java
    while (clazz != null) {
        try {
            return clazz.getDeclaredField(name)
        } catch (e: NoSuchFieldException) {
            clazz = clazz.superclass
        }
    }
    return null
}
