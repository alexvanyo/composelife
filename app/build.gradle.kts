plugins {
    id("com.android.application")
    kotlin("android")
}

android {
    compileSdk = 30
    buildToolsVersion = "30.0.3"

    lint {
        isWarningsAsErrors = true
        disable("ObsoleteLintCustomCheck")
    }

    defaultConfig {
        applicationId = "com.alexvanyo.composelife"
        minSdk = 21
        targetSdk = 30
        versionCode = 1
        versionName = "1.0"

        testInstrumentationRunner = "androidx.test.runner.AndroidJUnitRunner"
        vectorDrawables {
            useSupportLibrary = true
        }
    }

    buildTypes {
        release {
            isMinifyEnabled = true
            proguardFiles(getDefaultProguardFile("proguard-android-optimize.txt"), "proguard-rules.pro")
        }
    }
    compileOptions {
        sourceCompatibility = JavaVersion.VERSION_1_8
        targetCompatibility = JavaVersion.VERSION_1_8
    }
    kotlinOptions {
        jvmTarget = JavaVersion.VERSION_1_8.toString()
        freeCompilerArgs = listOf("-Werror")
    }
    buildFeatures {
        compose = true
    }
    composeOptions {
        kotlinCompilerExtensionVersion = libs.versions.compose.get()
    }
}

dependencies {
    implementation(libs.androidx.activityCompose)
    implementation(libs.androidx.appcompat)
    implementation(libs.androidx.compose.material)
    implementation(libs.androidx.compose.ui)
    implementation(libs.androidx.compose.uiTooling)
    implementation(libs.androidx.core)
    implementation(libs.androidx.lifecycle)
    implementation(libs.google.material)

    testImplementation(libs.junit4)

    androidTestImplementation(libs.androidx.compose.uiTestJunit4)
    androidTestImplementation(libs.androidx.espresso)
    androidTestImplementation(libs.androidx.test)
}