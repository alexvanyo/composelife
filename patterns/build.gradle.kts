plugins {
    id("com.alexvanyo.composelife.android.library")
    id("com.alexvanyo.composelife.android.library.ksp")
    id("com.alexvanyo.composelife.detekt")
}

android {
    defaultConfig {
        minSdk = 21
    }
}

dependencies {
    implementation(projects.algorithm)
    implementation(libs.androidx.compose.foundation)
    implementation(libs.sealedEnum.runtime)
    ksp(libs.sealedEnum.ksp)
}
