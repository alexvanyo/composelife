plugins {
    id("com.android.application")
    kotlin("android")
}

android {
    defaultConfig {
        testInstrumentationRunner = "androidx.test.runner.AndroidJUnitRunner"
    }

    testOptions {
        unitTests {
            isIncludeAndroidResources = true
        }
    }

    sourceSets {
        // Setup a shared test directory for instrumentation tests and Robolectric tests
        val sharedTestDir = "src/sharedTest/kotlin"
        getByName("test") {
            java.srcDir(sharedTestDir)
            resources.srcDir("src/sharedTest/resources")
        }
        getByName("androidTest") {
            java.srcDir(sharedTestDir)
        }
    }

    // Workaround for https://github.com/Kotlin/kotlinx.coroutines/blob/master/kotlinx-coroutines-debug/README.md#build-failures-due-to-duplicate-resource-files
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
}

tasks {
    withType<org.gradle.api.tasks.testing.Test> {
        useJUnitPlatform()

        // Automatically output Robolectric logs to stdout (for ease of debugging in Android Studio)
        systemProperty("robolectric.logging", "stdout")
    }
}
