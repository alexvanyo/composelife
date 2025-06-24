plugins {
    alias(libs.plugins.convention.kotlinMultiplatform)
    alias(libs.plugins.gradleDependenciesSorter)
}

kotlin {
    jvm()

    js {
        browser()
        nodejs()
    }
    wasmJs {
        browser()
    }

    macosX64()
    iosArm64(); iosX64()
    watchosArm32(); watchosArm64(); watchosX64()

    linuxArm64(); linuxX64()
    mingwX64()

    sourceSets {
        val commonTest by getting {
            dependencies {
                implementation(kotlin("test"))
            }
        }
    }
}
