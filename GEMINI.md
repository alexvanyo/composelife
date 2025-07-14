# Project: ComposeLife

This is a Kotlin Multiplatform (KMP) project that implements Conway's Game of Life. It serves as a personal sandbox for experimenting with modern libraries and tools.

## General Instructions & Architecture

- **Platforms:** The project targets Android (`app`), Wear OS (`wear`), and Desktop (`desktop-app`).
- **Language:** All code is written in Kotlin.
- **UI:** The user interface is built entirely with Jetpack Compose.
- **Build System:** The project uses Gradle with the Kotlin DSL (`.gradle.kts` files).
- **Architecture:** This is a multi-module project. Functionality is separated into layers like `data`, `database`, `algorithm`, and UI modules (`ui-mobile`, `ui-wear`, etc.).
- **Dependency Injection:** The project uses `kotlin-inject` and `kotlin-inject-anvil` for dependency injection.
- **Rendering:** The project uses advanced rendering techniques including AGSL, OpenGL, and SKSL.

## Coding Style & Conventions

When adding or modifying code, please adhere to the following conventions, which are enforced by CI using `detekt`.

- **File Headers:** All new `.kt` files **must** begin with the Apache 2.0 license header. Use the content from `config/license.template`.
- **Formatting:**
    - Standard Kotlin style guidelines apply.
    - **Trailing commas are required** on multi-line parameter lists and declaration sites.
    - Maximum line length is 120 characters.
- **Logging:** Use the `Kermit` logging library via the `logging` module. Do **not** use `android.util.Log`.
- **Forbidden Comments:** Do not use `FIXME:` or `STOPSHIP:`.
- **Dependencies:** Avoid introducing new external dependencies unless absolutely necessary. The project uses Renovate for automated dependency updates.

## Testing

- **Framework:** Use `kotlin.test` for all unit and integration tests. Do **not** use JUnit APIs directly (`org.junit.*`, `org.junit.jupiter.*`).
- **Screenshot Tests:** The project uses Roborazzi for screenshot testing.
- **Test Location:** Tests are organized hierarchically to be shared across platforms wherever possible. Place new tests in the appropriate source set (e.g., `commonTest`, `androidUnitTest`, `desktopTest`).

## Building and Running

- **Requirements:** JDK 21+ and Android Studio Narwhal 2025.1.1 or newer.
- **Build:** To check the entire project, run `./gradlew check`.
- **Run:** The primary runnable modules are:
    - `app`: The Android mobile application.
    - `desktop-app`: The JVM desktop application.
    - `wear`: The Wear OS watch face.
