import io.gitlab.arturbosch.detekt.Detekt
import org.jetbrains.kotlin.gradle.tasks.KotlinCompile
import org.jetbrains.kotlin.util.capitalizeDecapitalize.capitalizeAsciiOnly

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

plugins {
    id("com.alexvanyo.composelife.kotlin.multiplatform")
    id("com.alexvanyo.composelife.android.library")
    id("com.alexvanyo.composelife.detekt")
    alias(libs.plugins.wire)
}

android {
    namespace = "com.alexvanyo.composelife.preferencesproto"
    sourceSets["main"].manifest.srcFile("src/androidMain/AndroidManifest.xml")
    defaultConfig {
        minSdk = 21
    }
}

wire {
    sourcePath {
        srcDir("src/commonMain/proto")
    }
    kotlin {}
}

kotlin {
    jvm()
    android()

    sourceSets {
        val commonMain by getting {
            kotlin.srcDir("$buildDir/generated/source/wire/commonCommonMain")
            dependencies {
                api(libs.wire.runtime)
            }
        }
    }
}

tasks.withType<KotlinCompile>().configureEach {
    dependsOn("generateCommonCommonMainProtos")
}

tasks.withType<Detekt>().configureEach {
    dependsOn("generateCommonCommonMainProtos")
}
