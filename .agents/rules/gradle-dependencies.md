# Gradle Dependencies Rule

All dependency declarations for Gradle must be specified in `gradle/libs.versions.toml` (the version catalog).

## Guidelines

- Never hardcode dependency coordinate strings (e.g. `"group:artifact:version"`) directly in `build.gradle.kts` files.
- Declare dependency versions in the `[versions]` block of `gradle/libs.versions.toml`.
- Declare library artifacts in the `[libraries]` block of `gradle/libs.versions.toml`.
- Reference the library in `build.gradle.kts` using the type-safe catalog accessor (e.g. `libs.lean.runtime.kmp`).
- Keep dependency declarations in `build.gradle.kts` files and entries in `gradle/libs.versions.toml` properly sorted alphabetically (use `./gradlew sortDependencies`).
