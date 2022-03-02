plugins {
    id("com.alexvanyo.composelife.android.library")
    id("com.alexvanyo.composelife.detekt")
    kotlin("kapt")
}

android {
    defaultConfig {
        namespace = "com.alexvanyo.composelife.dispatchers"
        minSdk = 21
    }
}

dependencies {
    implementation(libs.kotlinx.coroutines.android)
    implementation(libs.kotlinx.coroutines.core)
    implementation(libs.dagger.hilt.runtime)
    kapt(libs.dagger.hilt.compiler)
}
