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
    implementation(libs.androidx.compose.uiTestJunit4)
    implementation(libs.sealedEnum.runtime)
    implementation(libs.jetbrains.kotlinx.coroutines.test)
    implementation(libs.jetbrains.kotlinx.datetime)
    ksp(libs.sealedEnum.ksp)
}
