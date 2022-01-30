import com.alexvanyo.composelife.buildlogic.sharedTestImplementation

plugins {
    id("com.alexvanyo.composelife.android.library")
    id("com.alexvanyo.composelife.android.library.compose")
    id("com.alexvanyo.composelife.android.library.gradlemanageddevices")
    id("com.alexvanyo.composelife.android.library.jacoco")
    id("com.alexvanyo.composelife.android.library.ksp")
    id("com.alexvanyo.composelife.android.library.testing")
    id("com.alexvanyo.composelife.detekt")
    kotlin("kapt")
}

android {
    defaultConfig {
        minSdk = 21
    }
}

dependencies {
    api(projects.parameterizedstring)
    api(projects.preferences)
    implementation(libs.androidx.compose.foundation)
    implementation(libs.androidx.compose.runtime)
    implementation(libs.androidx.compose.uiTestManifest)
    implementation(libs.jetbrains.kotlinx.datetime)
    implementation(libs.jetbrains.kotlinx.coroutines.android)
    implementation(libs.jetbrains.kotlinx.coroutines.core)
    implementation(libs.sealedEnum.runtime)
    ksp(libs.sealedEnum.ksp)
    implementation(libs.dagger.hilt.runtime)
    kapt(libs.dagger.hilt.compiler)

    sharedTestImplementation(libs.jetbrains.kotlinx.coroutines.test)
    sharedTestImplementation(libs.turbine)
    sharedTestImplementation(libs.androidx.compose.uiTestJunit4)
    sharedTestImplementation(libs.androidx.test.espresso)
    sharedTestImplementation(projects.testutil)
}
