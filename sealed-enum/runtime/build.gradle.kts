import org.jetbrains.kotlin.gradle.ExperimentalWasmDsl

plugins {
    alias(libs.plugins.convention.kotlinMultiplatform)
    alias(libs.plugins.gradleDependenciesSorter)
}

kotlin {
    jvm()

    js {
        browser {
            testTask {
                useKarma {
                    useChromiumHeadless()
                }
            }
        }
        nodejs {
            testTask {
                useKarma {
                    useChromiumHeadless()
                }
            }
        }
    }
    @OptIn(ExperimentalWasmDsl::class)
    wasmJs {
        browser {
            testTask {
                useKarma {
                    useChromiumHeadless()
                }
            }
        }
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
