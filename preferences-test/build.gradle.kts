import com.alexvanyo.composelife.buildlogic.sharedTestImplementation

plugins {
    id("com.alexvanyo.composelife.android.library")
    id("com.alexvanyo.composelife.android.library.gradlemanageddevices")
    id("com.alexvanyo.composelife.android.library.jacoco")
    id("com.alexvanyo.composelife.android.library.testing")
    id("com.alexvanyo.composelife.detekt")
    kotlin("kapt")
}

android {
    defaultConfig {
        minSdk = 21
    }

    lint {
        disable += setOf("JvmStaticProvidesInObjectDetector", "FieldSiteTargetOnQualifierAnnotation", "ModuleCompanionObjects", "ModuleCompanionObjectsNotInModuleParent")
    }
}

dependencies {
    api(projects.preferences)
    api(libs.dagger.hilt.runtime)
    api(libs.dagger.hilt.test)
    api(libs.androidx.test.junit)
    kapt(libs.dagger.hilt.compiler)

    sharedTestImplementation(libs.androidx.test.junit)

    kaptTest(libs.dagger.hilt.compiler)

    kaptAndroidTest(libs.dagger.hilt.compiler)
}
