package com.alexvanyo.composelife.buildlogic

import com.android.build.api.dsl.CommonExtension
import com.android.build.api.variant.AndroidComponentsExtension
import org.gradle.api.Project

fun Project.configureKsp(
    commonExtension: CommonExtension<*, *, *, *>,
    androidComponentsExtension: AndroidComponentsExtension<*, *, *>,
) {
    androidComponentsExtension.onVariants { applicationVariant ->
        commonExtension.sourceSets {
            getByName(applicationVariant.name) {
                java.srcDir(file("build/generated/ksp/${applicationVariant.name}/kotlin"))
            }
            getByName("test${applicationVariant.name.capitalize()}") {
                java.srcDir(file("build/generated/ksp/${applicationVariant.name}UnitTest/kotlin"))
            }
        }

        // TODO: Add explicit dependency to avoid "execution optimizations have been disabled to ensure correctness"
        afterEvaluate {
            tasks.getByName("lintAnalyze${applicationVariant.name.capitalize()}")
                .dependsOn("ksp${applicationVariant.name.capitalize()}UnitTestKotlin")
        }
    }
}
