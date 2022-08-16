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

import app.cash.paparazzi.gradle.PaparazziPlugin
import com.alexvanyo.composelife.buildlogic.ConventionPlugin
import com.alexvanyo.composelife.buildlogic.configureTesting
import com.android.build.api.variant.LibraryAndroidComponentsExtension
import com.android.build.gradle.LibraryExtension
import org.gradle.api.artifacts.VersionCatalogsExtension
import org.gradle.api.tasks.Delete
import org.gradle.api.tasks.testing.Test
import org.gradle.kotlin.dsl.configure
import org.gradle.kotlin.dsl.dependencies
import org.gradle.kotlin.dsl.getByType
import org.gradle.kotlin.dsl.register
import org.gradle.kotlin.dsl.withType

class AndroidLibraryPaparazziConventionPlugin : ConventionPlugin({
    with(pluginManager) {
        apply("com.android.library")
        apply("app.cash.paparazzi")
    }

    val libs = extensions.getByType<VersionCatalogsExtension>().named("libs")

    val libraryExtension = extensions.getByType<LibraryExtension>()

    configureTesting(libraryExtension)

    extensions.configure<LibraryAndroidComponentsExtension> {
        // Disable release builds for this test-only library, no need to run screenshot tests more than
        // once
        beforeVariants(selector().withBuildType("release")) { builder ->
            builder.enable = false
        }
    }

    dependencies {
        // Ensure we use the jre version of guava, since layoutlib requires it
        add("testImplementation", libs.findLibrary("guava.jre").get())
    }

    tasks.named("check") {
        // Ensure check is verifying the snapshots, see discussion in
        // https://github.com/cashapp/paparazzi/pull/421
        dependsOn("verifyPaparazziDebug")
    }

    tasks.register<Delete>("deletePaparazziSnapshots") {
        delete("${projectDir}/src/test/snapshots")
    }

    tasks.withType<PaparazziPlugin.PaparazziTask>().configureEach {
        if (name.contains("record")) {
            dependsOn("deletePaparazziSnapshots")
        }
    }

    tasks.withType<Test>().configureEach {
        // Increase memory and parallelize Paparazzi tests
        maxHeapSize = "2g"
        maxParallelForks = 1024
    }
})
