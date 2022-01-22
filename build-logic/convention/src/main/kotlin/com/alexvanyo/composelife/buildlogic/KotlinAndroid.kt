package com.alexvanyo.composelife.buildlogic

import com.android.build.api.dsl.CommonExtension
import org.gradle.api.JavaVersion
import org.gradle.api.Project
import org.gradle.api.artifacts.VersionCatalogsExtension
import org.gradle.kotlin.dsl.dependencies
import org.gradle.kotlin.dsl.getByType

fun Project.configureKotlinAndroid(
    commonExtension: CommonExtension<*, *, *, *>
) {
    val libs = extensions.getByType<VersionCatalogsExtension>().named("libs")

    commonExtension.apply {
        compileSdk = 32

        lint {
            warningsAsErrors = true
            disable.add("ObsoleteLintCustomCheck")
        }

        defaultConfig {
            vectorDrawables {
                useSupportLibrary = true
            }
        }

        compileOptions {
            sourceCompatibility = JavaVersion.VERSION_1_8
            targetCompatibility = JavaVersion.VERSION_1_8
            isCoreLibraryDesugaringEnabled = true
        }

        buildFeatures {
            compose = true
        }

        composeOptions {
            kotlinCompilerExtensionVersion = libs.findVersion("compose").get().toString()
        }
    }

    dependencies {
        add("coreLibraryDesugaring", libs.findLibrary("android.desugarJdkLibs").get())
    }
}
