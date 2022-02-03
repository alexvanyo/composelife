import com.alexvanyo.composelife.buildlogic.sharedTestImplementation

plugins {
    id("com.alexvanyo.composelife.android.library")
    id("com.alexvanyo.composelife.android.library.compose")
    id("com.alexvanyo.composelife.android.library.gradlemanageddevices")
    id("com.alexvanyo.composelife.android.library.jacoco")
    id("com.alexvanyo.composelife.android.library.testing")
    id("com.alexvanyo.composelife.arrowanalysis")
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

    sharedTestImplementation(libs.androidx.test.espresso)
    sharedTestImplementation(libs.androidx.compose.uiTestJunit4)
}
