# Module: resource-state

This module provides a generic way to represent the state of a resource that is being loaded asynchronously.

## Purpose & Architecture

- This is a Kotlin Multiplatform library module.
- It defines a sealed class called `ResourceState` that can represent the different states of a resource: `Loading`, `Success` (with the loaded data), and `Failure` (with an error).
- This is a common pattern used throughout the application to handle data that is loaded from a repository or other asynchronous source.
- It allows the UI to reactively observe the state of the resource and display the appropriate UI (e.g., a loading spinner, the content, or an error message).
- The module targets Android, Desktop (JVM), and WasmJs platforms.

## Usage

- Use `ResourceState` as the return type for functions in repositories or view models that load data asynchronously.
- In the UI, collect the `ResourceState` and use a `when` expression to handle the different states.

## Key Dependencies

- `org.jetbrains.compose.runtime`: For Jetpack Compose integration.
- `kotlinx-coroutines-core`: For asynchronous operations.
