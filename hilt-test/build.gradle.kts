plugins {
    id("com.alexvanyo.composelife.android.library")
    id("com.alexvanyo.composelife.detekt")
    kotlin("kapt")
}

android {
    defaultConfig {
        namespace = "com.alexvanyo.composelife.hilttest"
        minSdk = 21
    }
}

dependencies {
    api(projects.preferencesTest)
    api(libs.dagger.hilt.test)
    api(libs.androidx.test.runner)
    api(libs.kotlinx.coroutines.test)
    api(libs.androidx.compose.uiTestJunit4)
    kapt(libs.dagger.hilt.compiler)
}
