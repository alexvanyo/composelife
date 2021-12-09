plugins {
    id("com.alexvanyo.composelife.android.library")
    id("com.alexvanyo.composelife.android.library.gradlemanageddevices")
    id("com.alexvanyo.composelife.android.library.jacoco")
    id("com.alexvanyo.composelife.android.library.ksp")
    id("com.alexvanyo.composelife.android.library.testing")
    id("com.alexvanyo.composelife.detekt")
}

android {
    defaultConfig {
        minSdk = 21
    }
}

dependencies {
    implementation(libs.androidx.compose.foundation)
    implementation(libs.androidx.compose.runtime)
    implementation(libs.androidx.compose.uiTestManifest)
    implementation(libs.jetbrains.kotlinx.datetime)
    implementation(libs.jetbrains.kotlinx.coroutines.android)
    implementation(libs.jetbrains.kotlinx.coroutines.core)
    implementation(libs.sealedEnum.runtime)
    ksp(libs.sealedEnum.ksp)

    kspTest(libs.sealedEnum.ksp)
    testImplementation(libs.junit5.jupiter)
    testRuntimeOnly(libs.junit5.vintageEngine)
    testImplementation(libs.robolectric)
    testImplementation(libs.androidx.compose.uiTestJunit4)
    testImplementation(libs.androidx.compose.uiTestManifest)
    testImplementation(libs.jetbrains.kotlinx.coroutines.test)
    testImplementation(libs.turbine)
    testImplementation(projects.patterns)

    androidTestImplementation(libs.junit4)
    androidTestRuntimeOnly(libs.junit5.vintageEngine)
    androidTestImplementation(libs.androidx.compose.uiTestJunit4)
    androidTestImplementation(libs.androidx.espresso)
    androidTestImplementation(libs.androidx.test)
    androidTestImplementation(projects.patterns)
}
