import com.alexvanyo.composelife.buildlogic.configureAndroidCompose
import com.alexvanyo.composelife.buildlogic.configureKotlinAndroid

plugins {
    id("com.android.application")
    kotlin("android")
}

android {
    configureAndroidCompose(this)
}
