
plugins {
    id("com.alexvanyo.composelife.android.application")
    id("com.alexvanyo.composelife.android.application.gradlemanageddevices")
    id("com.alexvanyo.composelife.android.application.jacoco")
    id("com.alexvanyo.composelife.android.application.ksp")
    id("com.alexvanyo.composelife.android.application.testing")
    id("com.alexvanyo.composelife.detekt")
}

android {
    defaultConfig {
        applicationId = "com.alexvanyo.composelife"
        minSdk = 21
        targetSdk = 31
        versionCode = 1
        versionName = "1.0"
    }
}

dependencies {
    implementation(libs.accompanist.insets)
    implementation(libs.accompanist.systemuicontroller)
    implementation(libs.androidx.activityCompose)
    implementation(libs.androidx.compose.material)
    implementation(libs.androidx.compose.materialIconsExtended)
    implementation(libs.androidx.compose.ui)
    implementation(libs.androidx.compose.uiTooling)
    implementation(libs.androidx.compose.uiTestManifest)
    implementation(libs.androidx.core)
    implementation(libs.androidx.lifecycle)
    implementation(libs.jetbrains.kotlinx.datetime)
    implementation(libs.jetbrains.kotlinx.coroutines.android)
    implementation(libs.jetbrains.kotlinx.coroutines.core)
    implementation(libs.sealedEnum.runtime)
    ksp(libs.sealedEnum.ksp)

    debugImplementation(libs.square.leakCanary)

    kspTest(libs.sealedEnum.ksp)
    testImplementation(libs.junit5.jupiter)
    testRuntimeOnly(libs.junit5.vintageEngine)
    testImplementation(libs.robolectric)
    testImplementation(libs.androidx.compose.uiTestJunit4)
    testImplementation(libs.jetbrains.kotlinx.coroutines.test)
    testImplementation(libs.turbine)

    androidTestImplementation(libs.junit4)
    androidTestRuntimeOnly(libs.junit5.vintageEngine)
    androidTestImplementation(libs.androidx.compose.uiTestJunit4)
    androidTestImplementation(libs.androidx.espresso)
    androidTestImplementation(libs.androidx.test)
}
