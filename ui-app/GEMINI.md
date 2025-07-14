# Module: ui-app

This module is a Kotlin Multiplatform library containing Jetpack Compose UI components specifically for the main application targets (`:app` and `:desktop-app`).

## Purpose & Architecture

- This module provides UI components that are specific to the mobile and desktop application experience.
- It builds upon the foundational components in `:ui-common` and `:ui-mobile`.
- It is responsible for screen-level UI and state management for the main applications.

## Key Dependencies

- `:ui-common`: For core, reusable UI components.
- `:ui-mobile`: For shared mobile and desktop components.
- `:navigation`: For navigation logic.
- `:resource-state`: For handling asynchronous resource loading states.