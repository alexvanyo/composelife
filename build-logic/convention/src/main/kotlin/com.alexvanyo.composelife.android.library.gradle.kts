import com.alexvanyo.composelife.buildlogic.configureKotlinAndroid

plugins {
    id("com.android.library")
    kotlin("android")
}

android {
    configureKotlinAndroid(this)

    kotlinOptions {
        jvmTarget = JavaVersion.VERSION_1_8.toString()
        allWarningsAsErrors = true
        freeCompilerArgs = freeCompilerArgs + listOf("-Xopt-in=kotlin.RequiresOptIn")
    }
}
