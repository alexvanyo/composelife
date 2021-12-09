package com.alexvanyo.composelife.buildlogic

import com.android.build.api.dsl.CommonExtension
import gradle.kotlin.dsl.accessors._73ff8fab69e9dd87bad6b8a155a0213f.coreLibraryDesugaring
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
        compileSdk = 31

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
        coreLibraryDesugaring(libs.findDependency("android.desugarJdkLibs").get())
    }
}
