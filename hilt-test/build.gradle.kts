plugins {
    id("com.alexvanyo.composelife.android.library")
    id("com.alexvanyo.composelife.arrowanalysis")
    id("com.alexvanyo.composelife.detekt")
}

android {
    defaultConfig {
        minSdk = 21
    }
}

dependencies {
    api(libs.dagger.hilt.test)
    api(libs.androidx.test.runner)
}
