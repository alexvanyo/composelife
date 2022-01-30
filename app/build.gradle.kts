import com.alexvanyo.composelife.buildlogic.sharedTestImplementation

plugins {
    id("com.alexvanyo.composelife.android.application")
    id("com.alexvanyo.composelife.android.application.compose")
    id("com.alexvanyo.composelife.android.application.gradlemanageddevices")
    id("com.alexvanyo.composelife.android.application.jacoco")
    id("com.alexvanyo.composelife.android.application.ksp")
    id("com.alexvanyo.composelife.android.application.testing")
    id("com.alexvanyo.composelife.detekt")
    kotlin("kapt")
}

android {
    defaultConfig {
        applicationId = "com.alexvanyo.composelife"
        minSdk = 21
        targetSdk = 31
        versionCode = 1
        versionName = "1.0"
    }

    lint {
        disable += setOf("JvmStaticProvidesInObjectDetector", "FieldSiteTargetOnQualifierAnnotation", "ModuleCompanionObjects", "ModuleCompanionObjectsNotInModuleParent")
    }
}

dependencies {
    implementation(projects.algorithm)
    implementation(projects.dispatchers)

    implementation(libs.accompanist.insets)
    implementation(libs.accompanist.systemuicontroller)
    implementation(libs.androidx.activityCompose)
    implementation(libs.androidx.compose.material)
    implementation(libs.androidx.compose.materialIconsExtended)
    implementation(libs.androidx.compose.ui)
    implementation(libs.androidx.compose.uiTooling)
    implementation(libs.androidx.compose.uiTestManifest)
    implementation(libs.androidx.core)
    implementation(libs.androidx.hilt.navigation.compose)
    implementation(libs.androidx.lifecycle)
    implementation(libs.jetbrains.kotlinx.datetime)
    implementation(libs.jetbrains.kotlinx.coroutines.android)
    implementation(libs.jetbrains.kotlinx.coroutines.core)
    implementation(libs.sealedEnum.runtime)
    ksp(libs.sealedEnum.ksp)
    implementation(libs.dagger.hilt.runtime)
    kapt(libs.dagger.hilt.compiler)

    debugImplementation(libs.square.leakCanary)

    sharedTestImplementation(libs.androidx.compose.uiTestJunit4)
    sharedTestImplementation(libs.androidx.test.espresso)
    sharedTestImplementation(libs.androidx.test.junit)
    sharedTestImplementation(projects.testutil)
    sharedTestImplementation(projects.dispatchersTest)
    sharedTestImplementation(libs.jetbrains.kotlinx.coroutines.test)
    sharedTestImplementation(libs.turbine)

    kaptTest(libs.dagger.hilt.compiler)

    kaptAndroidTest(libs.dagger.hilt.compiler)
}

kapt {
    correctErrorTypes = true
}
