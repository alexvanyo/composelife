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
    }
}

dependencyResolutionManagement {
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
    }
}

plugins {
    id("com.gradle.develocity") version "4.1"
}

develocity {
    buildScan {
        termsOfUseUrl = "https://gradle.com/terms-of-service"
        termsOfUseAgree = "yes"

        obfuscation {
            username { "REDACTED" }
            hostname { "REDACTED" }
            ipAddresses { it.map { "0.0.0.0" } }
        }
    }
}

rootProject.name = "ComposeLife"
include(":algorithm")
include(":algorithm-benchmark")
include(":algorithm-test-resources")
include(":app")
include(":app-baseline-profile-generator")
include(":app-benchmark")
include(":app-compat-sync")
include(":clock")
include(":data")
include(":data-test-resources")
include(":database")
include(":database-test")
include(":desktop-app")
include(":dispatchers")
include(":dispatchers-test")
include(":do-not-keep-process")
include(":filesystem")
include(":filesystem-test")
include(":geometry")
include(":image-loader")
include(":inject-scopes")
include(":inject-test")
include(":kmp-android-runner")
include(":kmp-state-restoration-tester")
include(":logging")
include(":navigation")
include(":network")
include(":network-test")
include(":opengl-renderer")
include(":parameterized-string")
include(":parameterized-string-test-resources")
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
include(":roborazzi-showkase-screenshot-test")
include(":serialization")
include(":screenshot-test")
include(":session-value")
include(":strict-mode")
include(":test-activity")
include(":ui-app")
include(":ui-cells")
include(":ui-common")
include(":ui-common-screenshot-tests")
include(":ui-mobile")
include(":ui-settings")
include(":ui-tooling-preview")
include(":ui-wear")
include(":updatable")
include(":wear")
include(":wear-baseline-profile-generator")
include(":wear-watchface")
include(":wear-watchface-configuration")
include(":work")
include(":work-test")
