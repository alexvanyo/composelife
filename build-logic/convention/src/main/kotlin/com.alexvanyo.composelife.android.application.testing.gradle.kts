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

import com.alexvanyo.composelife.buildlogic.configureTesting
import com.slack.keeper.optInToKeeper

plugins {
    id("com.android.application")
    id("com.slack.keeper")
}

val libs = extensions.getByType<VersionCatalogsExtension>().named("libs")

android {
    defaultConfig {
        testBuildType = findProperty("com.alexvanyo.composelife.testBuildType") as String? ?: "staging"
    }

    androidComponents {
        beforeVariants { builder ->
            if (builder.buildType == "staging") {
                builder.optInToKeeper()
            }
        }
    }

    dependencies {
        keeperR8(libs.findLibrary("android.r8").get())
    }

    configureTesting(this)
}

keeper {
    automaticR8RepoManagement.set(false)
    traceReferences {}
}
