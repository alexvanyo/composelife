buildscript {
    repositories {
        google()
        mavenCentral()
    }
    dependencies {
        classpath("com.android.tools.build:gradle:7.0.3")
        classpath(kotlin("gradle-plugin", "1.5.31"))
    }
}

task<Delete>("clean") {
    delete(rootProject.buildDir)
}
