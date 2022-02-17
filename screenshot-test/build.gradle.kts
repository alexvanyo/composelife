plugins {
    id("com.alexvanyo.composelife.android.library")
    id("com.alexvanyo.composelife.detekt")
}

android {
    defaultConfig {
        minSdk = 21
    }
}

dependencies {
    implementation(libs.androidx.compose.foundation)
    implementation(libs.androidx.compose.uiTestJunit4)
    implementation(kotlin("test"))
}
