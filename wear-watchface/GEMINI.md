# Module: wear-watchface

This module contains the core implementation of the Game of Life watch face for Wear OS.

## Purpose & Architecture

- This is a Kotlin Multiplatform library module, primarily targeting Android for Wear OS.
- It implements the `WatchFaceService` from `androidx.wear.watchface`, which is the entry point for the watch face.
- It is responsible for rendering the watch face, handling user interactions, and managing complications.
- It likely depends on `:ui-wear` for Jetpack Compose components and `:algorithm` for the Game of Life simulation.

## Key Dependencies

- `:wear`: The application module that packages this watch face.
- `:ui-wear`: For Wear OS-specific Jetpack Compose components.
- `:algorithm`: For the core Game of Life logic.
- `androidx.wear.watchface`: The core library for creating watch faces.
