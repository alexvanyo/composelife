enableFeaturePreview("TYPESAFE_PROJECT_ACCESSORS")

pluginManagement {
    includeBuild("build-logic")
    repositories {
        google()
        mavenCentral()
        gradlePluginPortal()
    }
}

dependencyResolutionManagement {
    repositoriesMode.set(RepositoriesMode.FAIL_ON_PROJECT_REPOS)
    repositories {
        google()
        mavenCentral()
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
include(":hilt-test")
include(":parameterizedstring")
include(":preferences")
include(":preferences-test")
include(":testutil")
include(":wear")
