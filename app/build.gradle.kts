import org.jetbrains.kotlin.util.capitalizeDecapitalize.toLowerCaseAsciiOnly

plugins {
    id("com.android.application")
    kotlin("android")
    jacoco
    id("io.gitlab.arturbosch.detekt")
    alias(libs.plugins.ksp)
}

val jacocoTestReport = tasks.register("jacocoTestReport")

android {
    compileSdk = 31

    lint {
        warningsAsErrors = true
        disable.add("ObsoleteLintCustomCheck")
    }

    defaultConfig {
        applicationId = "com.alexvanyo.composelife"
        minSdk = 21
        targetSdk = 31
        versionCode = 1
        versionName = "1.0"

        testInstrumentationRunner = "androidx.test.runner.AndroidJUnitRunner"
        vectorDrawables {
            useSupportLibrary = true
        }
    }

    testOptions {
        unitTests {
            isIncludeAndroidResources = true
        }

        val deviceNames = listOf("Pixel 2", "Pixel 3 XL")
        val apiLevels = listOf(29, 30)

        devices {
            deviceNames.forEach { deviceName ->
                apiLevels.forEach { apiLevel ->
                    create<com.android.build.api.dsl.ManagedVirtualDevice>(
                        "${deviceName}api$apiLevel"
                            .toLowerCaseAsciiOnly()
                            .replace(" ", "")
                    ) {
                        this.device = deviceName
                        this.apiLevel = apiLevel
                        this.systemImageSource = "google"
                        this.abi = "x86"
                    }
                }
            }
        }
    }

    buildTypes {
        release {
            isMinifyEnabled = true
            isShrinkResources = true
            proguardFiles(getDefaultProguardFile("proguard-android-optimize.txt"), "proguard-rules.pro")
        }
    }

    sourceSets {
        val sharedTestDir = "src/sharedTest/kotlin"
        getByName("test") {
            java.srcDir(sharedTestDir)
            resources.srcDir("src/sharedTest/resources")
        }
        getByName("androidTest") {
            java.srcDir(sharedTestDir)
        }
    }

    compileOptions {
        sourceCompatibility = JavaVersion.VERSION_1_8
        targetCompatibility = JavaVersion.VERSION_1_8
        isCoreLibraryDesugaringEnabled = true
    }

    kotlinOptions {
        jvmTarget = JavaVersion.VERSION_1_8.toString()
        allWarningsAsErrors = true
        freeCompilerArgs = freeCompilerArgs + listOf("-Xopt-in=kotlin.RequiresOptIn")
    }

    buildFeatures {
        compose = true
    }

    composeOptions {
        kotlinCompilerExtensionVersion = libs.versions.compose.get()
    }

    packagingOptions {
        resources.excludes.addAll(
            listOf(
                "/META-INF/AL2.0",
                "/META-INF/LGPL2.1",
                "/META-INF/LICENSE.md",
                "/META-INF/LICENSE-notice.md"
            )
        )
    }

    androidComponents {
        onVariants { applicationVariant ->
            val testTaskName = "test${applicationVariant.name.capitalize()}UnitTest"

            val excludes = listOf(
                // Android
                "**/R.class",
                "**/R\$*.class",
                "**/BuildConfig.*",
                "**/Manifest*.*"
            )

            val reportTask = tasks.register("jacoco${testTaskName.capitalize()}Report", JacocoReport::class) {
                dependsOn(testTaskName)

                reports {
                    xml.required.set(true)
                    html.required.set(true)
                }

                classDirectories.setFrom(
                    fileTree("$buildDir/tmp/kotlin-classes/${applicationVariant.name}") {
                        exclude(excludes)
                    }
                )

                sourceDirectories.setFrom(files("$projectDir/src/main/java", "$projectDir/src/main/kotlin"))
                executionData.setFrom(file("$buildDir/jacoco/$testTaskName.exec"))
            }

            jacocoTestReport.get().dependsOn(reportTask)
        }

        onVariants { applicationVariant ->
            sourceSets {
                getByName(applicationVariant.name) {
                    java.srcDir(File("build/generated/ksp/${applicationVariant.name}/kotlin"))
                }
                getByName("test${applicationVariant.name.capitalize()}") {
                    java.srcDir(File("build/generated/ksp/${applicationVariant.name}UnitTest/kotlin"))
                }
            }
        }
    }
}

jacoco {
    toolVersion = libs.versions.jacoco.get()
}

detekt {
    buildUponDefaultConfig = true
    allRules = true
    autoCorrect = System.getenv("CI") != "true"
    config.setFrom("$rootDir/config/detekt.yml")
}

dependencies {
    detektPlugins(libs.detekt.formatting)

    coreLibraryDesugaring(libs.android.desugarJdkLibs)

    implementation(libs.accompanist.insets)
    implementation(libs.accompanist.systemuicontroller)
    implementation(libs.androidx.activityCompose)
    implementation(libs.androidx.compose.material)
    implementation(libs.androidx.compose.materialIconsExtended)
    implementation(libs.androidx.compose.ui)
    implementation(libs.androidx.compose.uiTooling)
    implementation(libs.androidx.compose.uiTestManifest)
    implementation(libs.androidx.core)
    implementation(libs.androidx.lifecycle)
    implementation(libs.jetbrains.kotlinx.datetime)
    implementation(libs.jetbrains.kotlinx.coroutines.android)
    implementation(libs.jetbrains.kotlinx.coroutines.core)
    implementation(libs.sealedEnum.runtime)
    ksp(libs.sealedEnum.ksp)

    debugImplementation(libs.square.leakCanary)

    kspTest(libs.sealedEnum.ksp)
    testImplementation(libs.junit5.jupiter)
    testRuntimeOnly(libs.junit5.vintageEngine)
    testImplementation(libs.robolectric)
    testImplementation(libs.androidx.compose.uiTestJunit4)
    testImplementation(libs.jetbrains.kotlinx.coroutines.test)
    testImplementation(libs.turbine)

    androidTestImplementation(libs.junit4)
    androidTestRuntimeOnly(libs.junit5.vintageEngine)
    androidTestImplementation(libs.androidx.compose.uiTestJunit4)
    androidTestImplementation(libs.androidx.espresso)
    androidTestImplementation(libs.androidx.test)
}

tasks {
    withType<io.gitlab.arturbosch.detekt.Detekt> {
        jvmTarget = JavaVersion.VERSION_1_8.toString()
    }

    withType<Test> {
        useJUnitPlatform()

        configure<JacocoTaskExtension> {
            // Required for JaCoCo + Robolectric
            // https://github.com/robolectric/robolectric/issues/2230
            isIncludeNoLocationClasses = true

            // Required for JDK 11 with the above
            // https://github.com/gradle/gradle/issues/5184#issuecomment-391982009
            excludes = listOf("jdk.internal.*")
        }

        // Automatically output Robolectric logs to stdout (for ease of debugging in Android Studio)
        systemProperty("robolectric.logging", "stdout")
    }

    getByName("check").dependsOn("detektMain")
}
