import org.jetbrains.kotlin.util.capitalizeDecapitalize.toLowerCaseAsciiOnly

plugins {
    id("com.android.application")
    kotlin("android")
    jacoco
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

    applicationVariants.all(closureOf<com.android.build.gradle.api.ApplicationVariant> {
        val testTaskName = "test${this@closureOf.name.capitalize()}UnitTest"

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
                files(
                    fileTree(this@closureOf.javaCompileProvider.get().destinationDirectory) {
                        exclude(excludes)
                    },
                    fileTree("$buildDir/tmp/kotlin-classes/${this@closureOf.name}") {
                        exclude(excludes)
                    }
                )
            )

            sourceDirectories.setFrom(this@closureOf.sourceSets.flatMap { it.javaDirectories + it.kotlinDirectories })
            executionData.setFrom(file("$buildDir/jacoco/$testTaskName.exec"))
        }

        jacocoTestReport.get().dependsOn(reportTask)
    })
}

dependencies {
    coreLibraryDesugaring(libs.android.desugarJdkLibs)

    implementation(libs.accompanist.insets)
    implementation(libs.accompanist.systemuicontroller)
    implementation(libs.androidx.activityCompose)
    implementation(libs.androidx.compose.material)
    implementation(libs.androidx.compose.ui)
    implementation(libs.androidx.compose.uiTooling)
    implementation(libs.androidx.compose.uiTestManifest)
    implementation(libs.androidx.core)
    implementation(libs.androidx.lifecycle)
    implementation(libs.jetbrains.kotlinx.datetime)

    debugImplementation(libs.square.leakCanary)

    testImplementation(libs.junit5.jupiter)
    testRuntimeOnly(libs.junit5.vintageEngine)
    testImplementation(libs.robolectric)
    testImplementation(libs.androidx.compose.uiTestJunit4)

    androidTestImplementation(libs.junit4)
    androidTestRuntimeOnly(libs.junit5.vintageEngine)
    androidTestImplementation(libs.androidx.compose.uiTestJunit4)
    androidTestImplementation(libs.androidx.espresso)
    androidTestImplementation(libs.androidx.test)
}

tasks {
    withType<Test> {
        useJUnitPlatform()

        configure<JacocoTaskExtension> {
            isIncludeNoLocationClasses = true
            excludes = listOf("jdk.internal.*")
        }
    }
}
