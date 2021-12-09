import com.alexvanyo.composelife.buildlogic.configureJacoco

plugins {
    id("com.android.library")
    jacoco
}

android {
    androidComponents {
        configureJacoco(this)
    }
}
