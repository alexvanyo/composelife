buildscript {
    repositories {
        google()
        mavenCentral()
    }
    dependencies {
        classpath("com.android.tools.build:gradle:7.1.0-alpha02")
        classpath(kotlin("gradle-plugin", "1.5.10"))
    }
}

task<Delete>("clean") {
    delete(rootProject.buildDir)
}
