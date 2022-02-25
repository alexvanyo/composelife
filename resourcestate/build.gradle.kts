import com.alexvanyo.composelife.buildlogic.sharedTestImplementation

plugins {
    id("com.alexvanyo.composelife.android.library")
    id("com.alexvanyo.composelife.android.library.compose")
    id("com.alexvanyo.composelife.android.library.gradlemanageddevices")
    id("com.alexvanyo.composelife.android.library.jacoco")
    id("com.alexvanyo.composelife.android.library.testing")
    id("com.alexvanyo.composelife.detekt")
}

android {
    defaultConfig {
        minSdk = 21
    }
}

dependencies {
    implementation(libs.kotlinx.coroutines.android)
    implementation(libs.androidx.compose.foundation)
    implementation(libs.androidx.compose.runtime)
    implementation(libs.androidx.compose.uiTestManifest)

    sharedTestImplementation(libs.kotlinx.coroutines.test)
    sharedTestImplementation(libs.turbine)
    sharedTestImplementation(libs.androidx.test.espresso)
    sharedTestImplementation(libs.androidx.compose.ui)
    sharedTestImplementation(libs.androidx.compose.uiTestJunit4)
}
