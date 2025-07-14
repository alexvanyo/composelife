# Module: ui-mobile

This module is a Kotlin Multiplatform library containing shared **Jetpack Compose UI components** for the mobile and desktop applications.

## Purpose & Architecture

- This module provides a common set of reusable UI components (`Composables`) that are shared between the `:app` and `:desktop-app` modules.
- It targets multiple platforms, including Android and Desktop (JVM).

## Source Code Structure

- **Shared Jetpack Compose code is located in `src/jbMain/kotlin`**. This is the primary location for common, reusable `@Composable` functions.
- Platform-specific UI tweaks or implementations can be placed in `src/androidMain` or `src/desktopMain`.
- Components in this module should be as stateless and reusable as possible.
- This module is intended for UI primitives, custom theme elements, and self-contained UI components (like custom cards, buttons, etc.). It should **not** contain complex business logic or screen-level state management.

## Previews

- To facilitate development and testing, create `@Preview` composables for the components in this module. This allows them to be viewed in Android Studio's Compose preview tool.
- TODO: Specify where `@Preview` files should be located.
