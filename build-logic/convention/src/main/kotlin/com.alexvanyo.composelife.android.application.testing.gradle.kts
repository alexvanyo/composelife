import com.alexvanyo.composelife.buildlogic.configureTesting

plugins {
    id("com.android.application")
}

android {
    configureTesting(this)
}
