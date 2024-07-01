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

import com.alexvanyo.composelife.buildlogic.FormFactor
import com.alexvanyo.composelife.buildlogic.configureGradleManagedDevices
import com.alexvanyo.composelife.buildlogic.jvmMolecule
import org.gradle.api.attributes.java.TargetJvmEnvironment.TARGET_JVM_ENVIRONMENT_ATTRIBUTE
import org.jetbrains.kotlin.gradle.InternalKotlinGradlePluginApi
import java.io.Serializable

plugins {
    alias(libs.plugins.convention.kotlinMultiplatform)
    alias(libs.plugins.convention.androidLibrary)
    alias(libs.plugins.convention.androidLibraryCompose)
    alias(libs.plugins.convention.androidLibraryJacoco)
    alias(libs.plugins.convention.androidLibraryKsp)
    alias(libs.plugins.convention.androidLibraryTesting)
    alias(libs.plugins.convention.detekt)
    alias(libs.plugins.convention.kotlinMultiplatformCompose)
    kotlin("plugin.serialization") version libs.versions.kotlin
    alias(libs.plugins.gradleDependenciesSorter)
}

android {
    namespace = "com.alexvanyo.composelife.ui.app"
    defaultConfig {
        minSdk = 21
    }
    configureGradleManagedDevices(setOf(FormFactor.Mobile), this)
}

kotlin {
    androidTarget()
    jvm("desktop")
    jvmMolecule(this)

    sourceSets {
        val commonMain by getting {
            dependencies {
                api(projects.algorithm)
                api(projects.clock)
                api(projects.data)
                api(projects.dispatchers)
                api(projects.random)

                implementation(libs.kotlinInject.runtime)
                implementation(libs.kotlinx.collections.immutable)
                implementation(libs.kotlinx.coroutines.core)
                implementation(libs.kotlinx.datetime)
                implementation(libs.kotlinx.serialization.json)
                implementation(projects.injectScopes)
                implementation(projects.navigation)
                implementation(projects.openglRenderer)
                implementation(projects.parameterizedString)
                implementation(projects.patterns)
                implementation(projects.resourceState)
                implementation(projects.sessionValue)
                implementation(projects.snapshotStateSet)
                implementation(projects.uiCommon)
                implementation(projects.uiToolingPreview)
            }
        }
        val jvmMain by creating {
            dependsOn(commonMain)
        }
        val moleculeMain by getting {
            dependsOn(jvmMain)
            configurations["kspMolecule"].dependencies.add(libs.sealedEnum.ksp.get())
        }
        val jbMain by creating {
            dependsOn(jvmMain)
            dependencies {
                api(libs.material3.windowSizeClass.multiplatform)

                implementation(libs.jetbrains.compose.material3)
                implementation(libs.jetbrains.compose.materialIconsExtended)
                implementation(libs.jetbrains.compose.ui)
                implementation(libs.jetbrains.compose.uiGeometry)
                implementation(libs.jetbrains.compose.uiUtil)
            }
        }
        val desktopMain by getting {
            dependsOn(jbMain)
            configurations["kspDesktop"].dependencies.add(libs.kotlinInject.ksp.get())
            configurations["kspDesktop"].dependencies.add(libs.sealedEnum.ksp.get())
            dependencies {
                implementation(compose.desktop.currentOs)
            }
        }
        val androidMain by getting {
            dependsOn(jbMain)
            configurations["kspAndroid"].dependencies.add(libs.kotlinInject.ksp.get())
            configurations["kspAndroid"].dependencies.add(libs.sealedEnum.ksp.get())
            dependencies {
                implementation(libs.androidx.activityCompose)
                implementation(libs.androidx.compose.animation)
                implementation(libs.androidx.compose.material3)
                implementation(libs.androidx.compose.materialIconsExtended)
                implementation(libs.androidx.compose.ui)
                implementation(libs.androidx.compose.uiTooling)
                implementation(libs.androidx.compose.uiUtil)
                implementation(libs.androidx.core)
                implementation(libs.androidx.lifecycle.runtime)
                implementation(libs.androidx.poolingContainer)
                implementation(libs.androidx.window)
                implementation(libs.kotlinx.coroutines.android)
                implementation(libs.sealedEnum.runtime)
                implementation(libs.sqldelight.androidDriver)
            }
        }
        val commonTest by getting {
            dependencies {
                implementation(libs.kotlinx.coroutines.test)
                implementation(libs.turbine)
                implementation(projects.dispatchersTest)
                implementation(projects.injectTestActivity)
                implementation(projects.kmpAndroidRunner)
                implementation(projects.kmpStateRestorationTester)
                implementation(projects.patterns)
                implementation(projects.preferencesTest)
                implementation(projects.screenshotTest)
                implementation(projects.testActivity)
            }
        }
        val jvmTest by creating {
            dependsOn(commonTest)
        }
        val jbTest by creating {
            dependsOn(jvmTest)
            dependencies {
                implementation(libs.jetbrains.compose.uiTestJunit4)
            }
        }
        val desktopTest by getting {
            dependsOn(jbTest)
            configurations["kspDesktopTest"].dependencies.add(libs.kotlinInject.ksp.get())
        }
        val androidSharedTest by getting {
            dependsOn(jbTest)
            dependencies {
                implementation(libs.androidx.compose.uiTestJunit4)
                implementation(libs.androidx.test.core)
                implementation(libs.androidx.test.espresso)
                implementation(libs.androidx.test.junit)
            }
        }
        val androidUnitTest by getting {
            configurations["kspAndroidTest"].dependencies.add(libs.kotlinInject.ksp.get())
        }
        val androidInstrumentedTest by getting {
            configurations["kspAndroidAndroidTest"].dependencies.add(libs.kotlinInject.ksp.get())
        }
    }
}
