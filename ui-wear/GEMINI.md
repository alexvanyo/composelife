# Module: ui-wear

This is a Kotlin Multiplatform library module containing **Jetpack Compose UI components** specifically for the Wear OS
target.

## Purpose & Architecture

- This module provides reusable `@Composable` functions tailored for the `:wear` module (the watch face).
- It contains UI components for rendering the watch face itself, as well as any configuration screens.
- It likely depends on the `androidx.wear.compose` libraries for Wear-specific components and layouts.

## Source Code Structure

- All source code is located in `src/androidMain/kotlin`.
- Components in this module should be designed for small, round, or square watch screens.
- This module should contain stateless, reusable UI components. Screen-level logic and state management belong in the `:wear` module.
