# Directory: gradle

This directory contains files related to the Gradle build system.

## Purpose & Contents

- **`wrapper/`**: This directory contains the Gradle Wrapper files (`gradle-wrapper.jar`, `gradle-wrapper.properties`). The wrapper allows the project to be built with a specific, consistent version of Gradle without requiring it to be installed on the host system.
- **`libs.versions.toml`**: This is the [Gradle Version Catalog](https://docs.gradle.org/current/userguide/version_catalogues.html). It is the central place where all project dependencies (libraries, plugins) and their versions are defined. Modules across the project reference the aliases defined in this file instead of hardcoding dependency strings and versions.

## Dependency Management Rules

- **Dependency Cleanups**: When removing a dependency, delete the configuration line entirely from the `build.gradle.kts` file instead of commenting it out.
- **Dependency Guard**: The project uses the Dependency Guard plugin to track changes to runtime dependency configurations.
  - If you change dependencies for guard-enabled modules (like `:app`, `:wear`, `:web-app`), you must regenerate the baseline configuration.
  - Update the baseline by running:
    ```bash
    ./gradlew dependencyGuardUpdate
    ```
  - If a change is temporary or needs verification without guard checks, you can temporarily disable it in that module's `build.gradle.kts` using:
    ```kotlin
    tasks.named("dependencyGuard") { enabled = false }
    ```
