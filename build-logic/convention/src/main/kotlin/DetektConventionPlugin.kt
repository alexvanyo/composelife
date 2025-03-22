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
import io.gitlab.arturbosch.detekt.Detekt
import io.gitlab.arturbosch.detekt.extensions.DetektExtension
import org.gradle.api.JavaVersion
import org.gradle.api.artifacts.VersionCatalogsExtension

class DetektConventionPlugin : ConventionPlugin({
    pluginManager.apply("io.gitlab.arturbosch.detekt")

    val libs = extensions.getByType(VersionCatalogsExtension::class.java).named("libs")

    extensions.configure(DetektExtension::class.java) {
        buildUponDefaultConfig = true
        allRules = true
        autoCorrect = true
        config.setFrom("$rootDir/config/detekt.yml")
        source.setFrom("src")
    }

    dependencies.add("detektPlugins", libs.findLibrary("detekt.formatting").get())

    tasks.withType(Detekt::class.java).configureEach {
        jvmTarget = JavaVersion.VERSION_17.toString()
    }

    tasks.named("check").configure {
        dependsOn(tasks.withType(Detekt::class.java))
    }
})
