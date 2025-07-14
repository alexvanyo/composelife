# Module: wear-watchface-configuration

This module provides the user interface for configuring the Game of Life watch face.

## Purpose & Architecture

- This is a Kotlin Multiplatform library module, primarily targeting Android.
- It contains the `Activity` and Jetpack Compose UI for the watch face's configuration screen.
- This UI allows users to customize aspects of the watch face, such as colors, speed, or patterns.

## Key Dependencies

- `:wear-watchface`: The watch face module it configures.
- `:ui-wear`: For Wear OS-specific Jetpack Compose components.
