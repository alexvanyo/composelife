package com.alexvanyo.composelife.buildlogic

import com.android.build.gradle.TestedExtension
import org.gradle.api.Project
import org.gradle.api.artifacts.VersionCatalogsExtension
import org.gradle.kotlin.dsl.DependencyHandlerScope
import org.gradle.kotlin.dsl.dependencies
import org.gradle.kotlin.dsl.getByType
import org.gradle.kotlin.dsl.kotlin
import org.gradle.kotlin.dsl.withType

fun Project.configureTesting(
    testedExtension: TestedExtension,
) {
    testedExtension.apply {
        defaultConfig {
            testInstrumentationRunner = "com.alexvanyo.composelife.HiltTestRunner"
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
    }

    val libs = extensions.getByType<VersionCatalogsExtension>().named("libs")

    dependencies {
        add("testImplementation", libs.findLibrary("junit5.jupiter").get())
        add("testRuntimeOnly", libs.findLibrary("junit5.vintageEngine").get())
        add("testImplementation", libs.findLibrary("robolectric").get())

        add("androidTestImplementation", libs.findLibrary("junit4").get())
        add("androidTestRuntimeOnly", libs.findLibrary("junit5.vintageEngine").get())

        sharedTestImplementation(kotlin("test"))
        sharedTestImplementation(project(":hilt-test"))
    }

    this.tasks.apply {
        withType<org.gradle.api.tasks.testing.Test> {
            useJUnitPlatform()

            // Automatically output Robolectric logs to stdout (for ease of debugging in Android Studio)
            systemProperty("robolectric.logging", "stdout")
        }
    }
}

/**
 * Adds the given dependency to both `testImplementation` and `androidTestImplementation`.
 */
fun DependencyHandlerScope.sharedTestImplementation(dependencyNotation: Any) {
    add("testImplementation", dependencyNotation)
    add("androidTestImplementation", dependencyNotation)
}

/**
 * Adds the given dependency to both `kaptTest` and `kaptAndroidTest`.
 */
fun DependencyHandlerScope.kaptSharedTest(dependencyNotation: Any) {
    add("kaptTest", dependencyNotation)
    add("kaptAndroidTest", dependencyNotation)
}
