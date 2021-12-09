import com.alexvanyo.composelife.buildlogic.configureKsp

plugins {
    id("com.android.application")
    id("com.google.devtools.ksp")
}

android {
    androidComponents {
        configureKsp(this@android, this)
    }
}
