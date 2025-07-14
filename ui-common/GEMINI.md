# Module: ui-common

This is a Kotlin Multiplatform library module that provides a set of fundamental, shared UI components and utilities used across the entire application.

## Purpose & Architecture

- This module is the foundation for the application's design system.
- It contains the most basic, reusable UI building blocks, such as custom buttons, text fields, dialogs, theme definitions, and color palettes.
- Other UI modules (`:ui-mobile`, `:ui-settings`, etc.) depend on this module for these core elements.

## Source Code Structure

- **`jbMain`**: Contains the primary, shared Jetpack Compose implementations of the common components.
- **`commonMain`**: Contains common data models or interfaces related to the UI components.
- Platform-specific source sets (`androidMain`, `desktopMain`) are used for any necessary platform-specific UI adjustments.

## Key Considerations

- Components in this module should be highly reusable, stateless, and have no external dependencies other than Jetpack Compose.
- When creating a new basic UI element that will be used in more than one place, it should be added to this module.
