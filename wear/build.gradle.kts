import com.alexvanyo.composelife.buildlogic.sharedTestImplementation

plugins {
    id("com.alexvanyo.composelife.android.application")
    id("com.alexvanyo.composelife.android.application.compose")
    id("com.alexvanyo.composelife.android.application.jacoco")
    id("com.alexvanyo.composelife.android.application.ksp")
    id("com.alexvanyo.composelife.android.application.testing")
    id("com.alexvanyo.composelife.detekt")
    kotlin("kapt")
}

android {
    defaultConfig {
        namespace = "com.alexvanyo.composelife.wear"
        applicationId = "com.alexvanyo.composelife.wear"
        minSdk = 26
        targetSdk = 30
        versionCode = 1
        versionName = "1.0"
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
    implementation(projects.algorithm)

    implementation(libs.androidx.compose.foundation)
    implementation(libs.androidx.compose.runtime)
    implementation(libs.androidx.core)
    implementation(libs.androidx.lifecycle)
    implementation(libs.androidx.wear.watchface)
    implementation(libs.kotlinx.datetime)
    implementation(libs.kotlinx.coroutines.android)
    implementation(libs.kotlinx.coroutines.core)
    implementation(libs.sealedEnum.runtime)
    ksp(libs.sealedEnum.ksp)
    implementation(libs.dagger.hilt.runtime)
    kapt(libs.dagger.hilt.compiler)

    debugImplementation(libs.square.leakCanary)

    sharedTestImplementation(libs.androidx.compose.uiTestJunit4)
    sharedTestImplementation(libs.androidx.test.espresso)
    sharedTestImplementation(libs.kotlinx.coroutines.test)
    sharedTestImplementation(libs.turbine)
}

kapt {
    correctErrorTypes = true
}
