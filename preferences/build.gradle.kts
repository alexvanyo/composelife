import com.alexvanyo.composelife.buildlogic.kaptSharedTest
import com.alexvanyo.composelife.buildlogic.sharedTestImplementation
import com.google.protobuf.gradle.protobuf

plugins {
    id("com.alexvanyo.composelife.android.library")
    id("com.alexvanyo.composelife.android.library.gradlemanageddevices")
    id("com.alexvanyo.composelife.android.library.jacoco")
    id("com.alexvanyo.composelife.android.library.testing")
    id("com.alexvanyo.composelife.detekt")
    alias(libs.plugins.protobuf)
    kotlin("kapt")
}

android {
    defaultConfig {
        minSdk = 21
    }

    lint {
        disable += setOf(
            "JvmStaticProvidesInObjectDetector",
            "FieldSiteTargetOnQualifierAnnotation",
            "ModuleCompanionObjects",
            "ModuleCompanionObjectsNotInModuleParent",
        )
    }
}

dependencies {
    api(projects.dispatchers)
    api(libs.protobuf.runtime) {
        // TODO: https://github.com/protocolbuffers/protobuf/issues/9517
        exclude("org.jetbrains.kotlin", "kotlin-test")
    }
    api(libs.kotlinx.coroutines.core)
    api(libs.kotlinx.coroutines.android)
    api(libs.androidx.dataStore)
    implementation(libs.dagger.hilt.runtime)
    kapt(libs.dagger.hilt.compiler)

    sharedTestImplementation(projects.preferencesTest)
    sharedTestImplementation(projects.dispatchersTest)
    sharedTestImplementation(libs.androidx.test.junit)
    sharedTestImplementation(libs.androidx.test.runner)
    sharedTestImplementation(libs.kotlinx.coroutines.test)
    sharedTestImplementation(libs.turbine)
    kaptSharedTest(libs.dagger.hilt.compiler)
}

protobuf {
    protoc(closureOf<com.google.protobuf.gradle.ExecutableLocator> {
        artifact = libs.protobuf.protoc.get().toString()
    })
    generateProtoTasks(closureOf<com.google.protobuf.gradle.ProtobufConfigurator.AndroidGenerateProtoTaskCollection> {
        all().forEach { task ->
            task.plugins(closureOf<NamedDomainObjectContainer<com.google.protobuf.gradle.GenerateProtoTask.PluginOptions>> {
                create("java") {
                    option("lite")
                }
                create("kotlin") {
                    option("lite")
                }
            })
        }
    })
}
