# Module: ui-tooling-preview

This module provides Jetpack Compose Previews for UI components, intended for use with Android Studio's tooling.

## Purpose & Architecture

- This is a Kotlin Multiplatform library module.
- It contains multi-`@Preview` annotations for use in other modules.
- This allows developers to easily visualize and interact with components in Android Studio's design view without running the full application.
- It helps in faster UI development and iteration.

## Key Dependencies

- `org.jetbrains.compose.ui:ui-tooling`: For the `@Preview` annotation and tooling support.
