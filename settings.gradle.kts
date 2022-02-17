enableFeaturePreview("TYPESAFE_PROJECT_ACCESSORS")

pluginManagement {
    includeBuild("build-logic")
    repositories {
        google()
        mavenCentral()
        maven(url = "https://storage.googleapis.com/r8-releases/raw") {
            content {
                includeModule("com.android.tools", "r8")
            }
        }
        gradlePluginPortal()
    }
}

dependencyResolutionManagement {
    repositoriesMode.set(RepositoriesMode.FAIL_ON_PROJECT_REPOS)
    repositories {
        google()
        mavenCentral()
        maven(url = "https://androidx.dev/snapshots/builds/8192674/artifacts/repository")
        maven(url = "https://storage.googleapis.com/r8-releases/raw") {
            content {
                includeModule("com.android.tools", "r8")
            }
        }
        maven(url = "https://jitpack.io") {
            content {
                includeGroup("com.github.livefront.sealed-enum")
            }
        }
    }
}

rootProject.name = "ComposeLife"
include(":algorithm")
include(":app")
include(":dispatchers")
include(":dispatchers-test")
include(":hilt-test")
include(":parameterizedstring")
include(":patterns")
include(":preferences")
include(":preferences-test")
include(":screenshot-test")
include(":wear")
