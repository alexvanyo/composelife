plugins {
    `kotlin-dsl`
}

group = "com.alexvanyo.composelife.buildlogic"

java {
    sourceCompatibility = JavaVersion.VERSION_1_8
    targetCompatibility = JavaVersion.VERSION_1_8
}

dependencies {
    implementation(libs.android.gradlePlugin)
    implementation(kotlin("gradle-plugin", libs.versions.kotlin.get()))
    implementation(libs.arrow.analysis.gradlePlugin)
    implementation(libs.detekt.gradlePlugin)
    implementation(libs.ksp.gradlePlugin)
}
