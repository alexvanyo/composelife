# Module: session-value

This module provides a utility for managing a value associated with a particular session, which is crucial for handling state updates between synchronous UI components (like `Slider` or `TextField`) and asynchronous data sources (like preferences saved to disk).

## Purpose & Architecture

- This is a Kotlin Multiplatform library module targeting Android, Desktop (JVM), and WasmJs.
- It solves the problem of state management where a UI component expects its state to be updated synchronously, but the underlying source of truth is asynchronous. A common example is a `Slider` controlling a value that is persisted to disk. Directly connecting the `Slider` to the asynchronous data source leads to a poor user experience because the UI doesn't update immediately.
- The core data structure is `SessionValue<T>`, which wraps a value with a `sessionId` and a `valueId`. These UUIDs allow for robustly distinguishing between different update sessions and specific value changes within those sessions.
- This system allows UI components to maintain a local, synchronous copy of the state for a responsive user experience, while correctly handling updates from the asynchronous "upstream" source. It can differentiate between:
    - An update from the local session being reflected back.
    - An update from a different session, which should invalidate the local state.
- The primary entry point is the `rememberSessionValueHolder` composable, which manages the interaction between the upstream (asynchronous) `SessionValue` and the local (synchronous) UI state.

## Usage

- Use `rememberSessionValueHolder` in composables that need to edit a value from an asynchronous data source with a UI component that expects synchronous updates.
- This pattern is explained in detail in the module's README, covering both "confirm/cancel" and "continuous update" scenarios.

## Key Dependencies

- `org.jetbrains.compose.runtime`: For Jetpack Compose integration.
- `org.jetbrains.compose.runtime.saveable`: To allow `SessionValue` to be saved and restored.
- `:serialization`: For custom serialization logic.
- `:logging`: For logging.

See the [README.md](README.md) for a detailed explanation and examples.