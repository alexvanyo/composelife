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

enableFeaturePreview("TYPESAFE_PROJECT_ACCESSORS")

pluginManagement {
    includeBuild("build-logic")
    repositories {
        maven(url = "https://storage.googleapis.com/r8-releases/raw") {
            content {
                includeModule("com.android.tools", "r8")
            }
        }
        google()
        mavenCentral()
        gradlePluginPortal()
        maven(url = "https://maven.pkg.jetbrains.space/public/p/compose/dev")
    }
}

dependencyResolutionManagement {
    repositoriesMode.set(RepositoriesMode.FAIL_ON_PROJECT_REPOS)
    repositories {
        maven(url = "https://storage.googleapis.com/r8-releases/raw") {
            content {
                includeModule("com.android.tools", "r8")
            }
        }
        maven(url = "https://jitpack.io") {
            content {
                includeGroup("com.github.livefront.sealed-enum")
            }
        }
        google()
        mavenCentral()
        maven(url = "https://maven.pkg.jetbrains.space/public/p/compose/dev")
    }
}

rootProject.name = "ComposeLife"
include(":algorithm")
include(":app")
include(":app-baseline-profile-generator")
include(":app-benchmark")
include(":app-compat-sync")
include(":clock")
include(":data")
include(":database")
include(":database-test")
include(":dispatchers")
include(":dispatchers-test")
include(":do-not-keep-process")
include(":geometry")
include(":hilt-test")
include(":hilt-test-activity")
include(":kmp-android-runner")
include(":kmp-state-restoration-tester")
include(":navigation")
include(":opengl-renderer")
include(":parameterized-string")
include(":patterns")
include(":preferences")
include(":preferences-proto")
include(":preferences-test")
include(":process-lifecycle")
include(":random")
include(":resource-state")
include(":resources-app")
include(":resources-common")
include(":resources-wear")
include(":screenshot-test")
include(":snapshot-state-set")
include(":test-activity")
include(":ui-app")
include(":ui-app-screenshots")
include(":ui-common")
include(":ui-wear")
include(":ui-wear-screenshots")
include(":updatable")
include(":wear")
include(":wear-baseline-profile-generator")
include(":wear-watchface")
include(":wear-watchface-configuration")
