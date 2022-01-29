package com.alexvanyo.composelife.buildlogic

import com.android.build.gradle.TestedExtension
import org.gradle.api.Project
import org.gradle.kotlin.dsl.withType

fun Project.configureTesting(
    testedExtension: TestedExtension
) {
    testedExtension.apply {
        defaultConfig {
            testInstrumentationRunner = "androidx.test.runner.AndroidJUnitRunner"
        }

        testOptions {
            unitTests {
                isIncludeAndroidResources = true
            }
        }

        sourceSets {
            // Setup a shared test directory for instrumentation tests and Robolectric tests
            val sharedTestDir = "src/sharedTest/kotlin"
            val sharedResDir = "src/sharedTest/res"
            getByName("test") {
                java.srcDir(sharedTestDir)
                res.srcDir(sharedResDir)
                resources.srcDir("src/sharedTest/resources")
            }
            getByName("androidTest") {
                java.srcDir(sharedTestDir)
                res.srcDir(sharedResDir)
            }
        }

        // Workaround for https://github.com/Kotlin/kotlinx.coroutines/blob/master/kotlinx-coroutines-debug/README.md#build-failures-due-to-duplicate-resource-files
        packagingOptions {
            resources.excludes.addAll(
                listOf(
                    "/META-INF/AL2.0",
                    "/META-INF/LGPL2.1",
                    "/META-INF/LICENSE.md",
                    "/META-INF/LICENSE-notice.md"
                )
            )
        }
    }

    this.tasks.apply {
        withType<org.gradle.api.tasks.testing.Test> {
            useJUnitPlatform()

            // Automatically output Robolectric logs to stdout (for ease of debugging in Android Studio)
            systemProperty("robolectric.logging", "stdout")
        }
    }
}
