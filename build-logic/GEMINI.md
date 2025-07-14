# Directory: build-logic

This directory contains custom **Gradle Convention Plugins** that standardize build configurations across all modules in the project.

## Purpose & Architecture

The purpose of this module is to enforce consistency and reduce boilerplate in the `build.gradle.kts` files of other modules. Instead of configuring plugins and settings in each module, we apply a pre-configured convention plugin from this directory.

When you need to change a build setting, dependency, or plugin version that affects multiple modules, the change should be made here in the relevant convention plugin.

## Convention Plugins

The plugins are located in `convention/src/main/kotlin`. They are grouped by module type:

-   **`AndroidApplication...`**: Convention plugins for a main, runnable Android application module (i.e., `:app`).
-   **`AndroidLibrary...`**: Convention plugins for Android library modules.
-   **`KotlinMultiplatform...`**: Convention plugins for Kotlin Multiplatform library modules.
-   **`AndroidTest...`**: Convention plugins for Android test modules.

There are also specialized plugins for setting up specific tools and frameworks, such as:

-   `...ComposeConventionPlugin`: Applies Jetpack Compose settings.
-   `...JacocoConventionPlugin`: Configures JaCoCo for code coverage.
-   `...KspConventionPlugin`: Configures KSP (Kotlin Symbol Processing).
-   `...RoborazziConventionPlugin`: Configures Roborazzi for screenshot tests.
-   `DetektConventionPlugin.kt`: Configures the Detekt static analysis tool.

## Usage

When creating a new module, you should apply the appropriate convention plugin(s) in its `build.gradle.kts` file. For example, a new Android library using Compose would apply `com.alexvanyo.composelife.android.library` and `com.alexvanyo.composelife.android.library.compose`.
