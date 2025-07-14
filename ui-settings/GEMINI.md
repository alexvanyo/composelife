# Module: ui-settings

This is a Kotlin Multiplatform library module that provides the user interface for the application's settings screens.

## Purpose & Architecture

- This module contains reusable `@Composable` functions for displaying and interacting with application settings.
- It is shared between the `:app` and `:desktop-app` modules to provide a consistent settings experience.
- It likely depends on the `:preferences` module to read and write setting values.
- It may also depend on `:ui-common` for basic UI building blocks.

## Source Code Structure

- **`jbMain`**: Contains the primary, shared Jetpack Compose implementation of the settings UI.
- **`commonMain`**: May contain view models or state holders for the settings UI.
- Platform-specific source sets (`androidMain`, `desktopMain`) are used for any necessary platform-specific UI adjustments.
