import com.alexvanyo.composelife.buildlogic.configureKsp

plugins {
    id("com.android.library")
    id("com.google.devtools.ksp")
}

android {
    androidComponents {
        configureKsp(this@android, this)
    }
}
