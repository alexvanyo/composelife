buildscript {
    repositories {
        google()
        mavenCentral()
    }
    dependencies {
        classpath("com.android.tools.build:gradle:7.2.0-alpha03")
        classpath(kotlin("gradle-plugin", "1.5.31"))
    }
}

task<Delete>("clean") {
    delete(rootProject.buildDir)
}
