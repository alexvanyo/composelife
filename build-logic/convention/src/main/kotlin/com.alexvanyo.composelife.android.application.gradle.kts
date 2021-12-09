import com.alexvanyo.composelife.buildlogic.configureKotlinAndroid

plugins {
    id("com.android.application")
    kotlin("android")
}

val libs = extensions.getByType<VersionCatalogsExtension>().named("libs")

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
    }

    compileOptions {
        isCoreLibraryDesugaringEnabled = true
    }

    kotlinOptions {
        jvmTarget = JavaVersion.VERSION_1_8.toString()
        allWarningsAsErrors = true
        freeCompilerArgs = freeCompilerArgs + listOf("-Xopt-in=kotlin.RequiresOptIn")
    }
}

dependencies {
    coreLibraryDesugaring(libs.findDependency("android.desugarJdkLibs").get())
}
