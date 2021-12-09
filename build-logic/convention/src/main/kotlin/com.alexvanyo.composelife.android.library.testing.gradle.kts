import com.alexvanyo.composelife.buildlogic.configureTesting

plugins {
    id("com.android.library")
}

android {
    configureTesting(this)
}
