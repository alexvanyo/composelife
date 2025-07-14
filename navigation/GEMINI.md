# Module: navigation

This module provides the navigation framework for the application.

## Purpose & Architecture

- This is a Kotlin Multiplatform library module responsible for pane navigation and state management within the UI.
- It is built on top of Jetpack Compose and uses the [Circuit](https://slackhq.github.io/circuit/) library (`circuit-retained`) for building a pane-based navigation system.
- It defines the core components for navigating between different panes (`Pane`s) and managing the back stack.
- The logic is shared between Android and Desktop targets.

## Key Dependencies

- `circuit-retained`: The core library for state management and navigation.
- `org.jetbrains.compose.ui`: For Jetpack Compose UI components.
- `org.jetbrains.compose.animation`: For handling pane transitions.
- `:kmp-state-restoration-tester`: For testing state restoration of the navigation state.

See the [navigation documentation](../docs/navigation.md) for more detailed information.
