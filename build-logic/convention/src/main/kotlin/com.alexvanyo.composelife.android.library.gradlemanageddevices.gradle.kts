import com.alexvanyo.composelife.buildlogic.configureGradleManagedDevices

plugins {
    id("com.android.library")
}

android {
    configureGradleManagedDevices(this)
}
