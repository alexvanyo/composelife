import com.alexvanyo.composelife.buildlogic.kaptSharedTest
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
        namespace = "com.alexvanyo.composelife"
        applicationId = "com.alexvanyo.composelife"
        minSdk = 21
        targetSdk = 32
        versionCode = 1
        versionName = "1.0"
    }

    lint {
        disable += setOf(
            "JvmStaticProvidesInObjectDetector",
            "FieldSiteTargetOnQualifierAnnotation",
            "ModuleCompanionObjects",
            "ModuleCompanionObjectsNotInModuleParent",
        )
    }
}

dependencies {
    implementation(projects.algorithm)
    implementation(projects.dispatchers)
    implementation(projects.hiltTestActivity)
    implementation(projects.navigation)
    implementation(projects.resourceState)

    implementation(libs.accompanist.systemuicontroller)
    implementation(libs.androidx.activityCompose)
    implementation(libs.androidx.compose.material3)
    implementation(libs.androidx.compose.materialIconsExtended)
    implementation(libs.androidx.compose.ui)
    implementation(libs.androidx.compose.uiToolingPreview)
    implementation(libs.androidx.compose.uiTestManifest)
    implementation(libs.androidx.core)
    implementation(libs.androidx.hilt.navigation.compose)
    implementation(libs.androidx.lifecycle)
    implementation(libs.kotlinx.datetime)
    implementation(libs.kotlinx.coroutines.android)
    implementation(libs.kotlinx.coroutines.core)
    implementation(libs.sealedEnum.runtime)
    ksp(libs.sealedEnum.ksp)
    implementation(libs.dagger.hilt.runtime)
    kapt(libs.dagger.hilt.compiler)

    debugImplementation(libs.androidx.compose.uiTooling)
    debugImplementation(libs.square.leakCanary)

    sharedTestImplementation(projects.dispatchersTest)
    sharedTestImplementation(projects.patterns)
    sharedTestImplementation(projects.preferencesTest)
    sharedTestImplementation(projects.screenshotTest)
    sharedTestImplementation(libs.androidx.compose.uiTestJunit4)
    sharedTestImplementation(libs.androidx.test.espresso)
    sharedTestImplementation(libs.androidx.test.junit)
    sharedTestImplementation(libs.kotlinx.coroutines.test)
    sharedTestImplementation(libs.turbine)
    kaptSharedTest(libs.dagger.hilt.compiler)
}

kapt {
    correctErrorTypes = true
}
