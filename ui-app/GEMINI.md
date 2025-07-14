# Module: ui-app

This module is the primary UI layer, assembling all other UI and data modules into the complete application interface.

## Purpose & Architecture

- This is a Kotlin Multiplatform library module that contains the main UI for the mobile and desktop applications.
- It acts as the central integration point for most other modules in the project. It brings together the algorithm, data, preferences, and various UI components (`:ui-cells`, `:ui-common`, `:ui-settings`, etc.) to construct the final user interface.
- It contains the top-level `@Composable` functions that represent the main application screens and orchestrates the navigation between them using the `:navigation` module.
- It is responsible for observing state from the data layer and passing it down to the appropriate UI components.

## Key Dependencies

- `:algorithm`, `:data`, `:preferences`: For accessing the core logic and data of the application.
- `:ui-cells`, `:ui-common`, `:ui-mobile`, `:ui-settings`: For the building blocks of the UI.
- `:navigation`: For handling screen navigation.
- `:dispatchers`, `:resource-state`, `:session-value`: For managing state and asynchrony.
- `org.jetbrains.compose.material3`: For the Material Design components.
- `showkase`: For generating a component browser for the UI.
- `roborazzi`: For screenshot testing the UI components.
