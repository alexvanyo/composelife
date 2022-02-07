import com.alexvanyo.composelife.buildlogic.configureKotlinAndroid

plugins {
    id("com.android.application")
    kotlin("android")
}

android {
    configureKotlinAndroid(this)

    signingConfigs {
        getByName("debug") {
            keyAlias = "debug"
            keyPassword = "android"
            storeFile = file("$rootDir/keystore/debug.jks")
            storePassword = "android"
        }
    }

    buildTypes {
        debug {
            signingConfig = signingConfigs.getByName("debug")
        }

        release {
            isMinifyEnabled = true
            isShrinkResources = true
            proguardFiles(getDefaultProguardFile("proguard-android-optimize.txt"), "proguard-rules.pro")
        }

        // Create a build type for the purposes of testing a minified build (like release is)
        create("staging") {
            isMinifyEnabled = true // minify like a release build
            isShrinkResources = true // shrink resources like a release build
            matchingFallbacks.add("release") // fallback to release for dependencies
            signingConfig = signingConfigs.getByName("debug") // sign with debug for testing
            // Use the normal proguard rules, as well as some additional staging ones just for tests (when needed)
            proguardFiles(
                getDefaultProguardFile("proguard-android-optimize.txt"),
                "proguard-rules.pro",
                "staging-proguard-rules.pro"
            )
        }
    }

    kotlinOptions {
        jvmTarget = JavaVersion.VERSION_1_8.toString()
        allWarningsAsErrors = true
        freeCompilerArgs = freeCompilerArgs + listOf("-Xopt-in=kotlin.RequiresOptIn")
    }
}
