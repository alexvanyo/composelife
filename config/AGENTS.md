# Directory: config

This directory contains project-wide configuration files.

## Purpose & Contents

- This directory is not a source module but holds configuration files that apply to the entire project.
- **`detekt.yml`**: This is the configuration file for [Detekt](https://detekt.dev/), the static code analysis tool used for Kotlin. It defines the rulesets, formatting guidelines, and thresholds that are enforced across all modules.
- **`license.template`**: This file contains the Apache 2.0 license header that must be present at the top of every `.kt` source file, as specified in the root `AGENTS.md`.

## Centralized Version Upgrades

- **SDK Versions**: Target SDK versions (e.g., `compileSdk`, `targetSdk`, `minSdk`) are defined in the central version catalog `gradle/libs.versions.toml` or customized in convention plugins under `build-logic`. Never hardcode SDK versions inside module `build.gradle.kts` files.
- **Robolectric Configuration**: When updating the `compileSdk` to a newer version (e.g., API 37), make sure Robolectric is updated to support the corresponding API version. This is typically configured in the version catalog and via the global test resources.
