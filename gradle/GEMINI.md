# Directory: gradle

This directory contains files related to the Gradle build system.

## Purpose & Contents

- **`wrapper/`**: This directory contains the Gradle Wrapper files (`gradle-wrapper.jar`, `gradle-wrapper.properties`). The wrapper allows the project to be built with a specific, consistent version of Gradle without requiring it to be installed on the host system.
- **`libs.versions.toml`**: This is the [Gradle Version Catalog](https://docs.gradle.org/current/userguide/version_catalogues.html). It is the central place where all project dependencies (libraries, plugins) and their versions are defined. Modules across the project reference the aliases defined in this file instead of hardcoding dependency strings and versions.
