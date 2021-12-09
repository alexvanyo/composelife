import com.alexvanyo.composelife.buildlogic.configureGradleManagedDevices

plugins {
    id("com.android.application")
}

android {
    configureGradleManagedDevices(this)
}
