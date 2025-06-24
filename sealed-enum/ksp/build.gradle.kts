plugins {
    alias(libs.plugins.convention.kotlinMultiplatform)
    alias(libs.plugins.gradleDependenciesSorter)
    alias(libs.plugins.ksp)
}

kotlin {
    jvm()

    sourceSets {
        val jvmMain by getting {
            configurations["kspJvm"].dependencies.addAll(
                listOf(
                    libs.autoService.ksp.get(),
                )
            )
            dependencies {
                implementation(libs.autoService.annotations)
                implementation(libs.kotlinPoet)
                implementation(libs.kotlinPoet.ksp)
                implementation(projects.sealedEnum.processingCommon)
                implementation(projects.sealedEnum.runtime)

                compileOnly(libs.ksp.api)
            }
        }
    }
}
