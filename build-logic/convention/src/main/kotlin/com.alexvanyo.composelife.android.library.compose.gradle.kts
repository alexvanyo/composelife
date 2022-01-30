import com.alexvanyo.composelife.buildlogic.configureAndroidCompose

plugins {
    id("com.android.library")
    kotlin("android")
}

android {
    configureAndroidCompose(this)
}
