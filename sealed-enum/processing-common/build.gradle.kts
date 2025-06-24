plugins {
    alias(libs.plugins.convention.kotlinMultiplatform)
    alias(libs.plugins.gradleDependenciesSorter)
}

tasks.withType<Test> {
    useJUnitPlatform()
}

kotlin {
    jvm()

    sourceSets {
        val jvmMain by getting {
            dependencies {
                implementation(libs.kotlinPoet)
                implementation(projects.sealedEnum.runtime)
            }
        }
        val jvmTest by getting {
            dependencies {
                implementation(kotlin("test"))
                implementation(libs.junit.jupiter)
            }
        }
    }
}


