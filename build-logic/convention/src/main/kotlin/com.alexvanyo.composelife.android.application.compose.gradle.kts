import com.alexvanyo.composelife.buildlogic.configureAndroidCompose

plugins {
    id("com.android.application")
    kotlin("android")
}

android {
    configureAndroidCompose(this)
}
