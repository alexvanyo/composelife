plugins {
    id("com.alexvanyo.composelife.android.library")
    id("com.alexvanyo.composelife.detekt")
    kotlin("kapt")
}

android {
    defaultConfig {
        namespace = "com.alexvanyo.composelife.hilttestactivity"
        minSdk = 21
    }
}

dependencies {
    api(libs.dagger.hilt.runtime)
    kapt(libs.dagger.hilt.compiler)
}

kapt {
    correctErrorTypes = true
}
