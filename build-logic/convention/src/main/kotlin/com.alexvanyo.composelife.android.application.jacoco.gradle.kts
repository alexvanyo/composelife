import com.alexvanyo.composelife.buildlogic.configureJacoco

plugins {
    id("com.android.application")
    jacoco
}

android {
    androidComponents {
        configureJacoco(this)
    }
}
