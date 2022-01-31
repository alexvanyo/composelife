plugins {
    id("com.alexvanyo.composelife.android.library")
    id("com.alexvanyo.composelife.detekt")
    kotlin("kapt")
}

android {
    defaultConfig {
        minSdk = 21
    }
}

dependencies {
    api(projects.dispatchers)
    api(libs.androidx.compose.uiTestJunit4)
    api(libs.kotlinx.coroutines.test)
    api(libs.kotlinx.datetime)
    api(libs.dagger.hilt.runtime)
    api(libs.dagger.hilt.test)
    api(libs.androidx.test.junit)
    kapt(libs.dagger.hilt.compiler)
}
