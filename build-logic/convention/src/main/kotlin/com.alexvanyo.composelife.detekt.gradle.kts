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
    id("io.gitlab.arturbosch.detekt")
}

val libs = extensions.getByType<VersionCatalogsExtension>().named("libs")

detekt {
    buildUponDefaultConfig = true
    allRules = true
    autoCorrect = System.getenv("CI") != "true"
    config.setFrom("$rootDir/config/detekt.yml")
    source = files(
        "src/main/kotlin",
        "src/test/kotlin",
        "src/androidTest/kotlin",
        "src/sharedTest/kotlin"
    )
}

dependencies {
    detektPlugins(libs.findLibrary("detekt.formatting").get())
}

tasks {
    withType<io.gitlab.arturbosch.detekt.Detekt> {
        jvmTarget = JavaVersion.VERSION_1_8.toString()
    }

    getByName("check").dependsOn("detektMain")
}
