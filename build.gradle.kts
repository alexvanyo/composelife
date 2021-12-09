plugins {
    id("com.alexvanyo.composelife.mergejacoco")
}

buildscript {
    repositories {
        google()
        mavenCentral()
    }
    dependencies {
        classpath(libs.android.gradlePlugin)
        classpath(kotlin("gradle-plugin", libs.versions.kotlin.get()))
    }
}

task<Delete>("clean") {
    delete(rootProject.buildDir)
}
