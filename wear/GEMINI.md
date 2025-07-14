# Module: wear

This module contains the **Wear OS watch face**.

## Purpose & Architecture

- This module implements a Game of Life watch face using Jetpack Compose for Wear OS and the `androidx.wear.watchface` libraries.
- The core of this module is the `WatchFaceService` implementation, which is responsible for rendering the watch face.
- It depends on shared modules like `:algorithm` for the simulation logic and `:ui-wear` for Compose components.
- This module also likely contains related components, such as configuration activities for the watch face.

## Build Variants

- This module has a `staging` build variant (`src/androidStaging`), which may have different configurations from the release version.
