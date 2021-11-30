enableFeaturePreview("VERSION_CATALOGS")
enableFeaturePreview("TYPESAFE_PROJECT_ACCESSORS")

dependencyResolutionManagement {
    repositoriesMode.set(RepositoriesMode.FAIL_ON_PROJECT_REPOS)
    repositories {
        google()
        mavenCentral()
        maven(url = "https://androidx.dev/snapshots/builds/7952994/artifacts/repository")
        maven(url = "https://jitpack.io")
    }
}

rootProject.name = "ComposeLife"
include(":app")
