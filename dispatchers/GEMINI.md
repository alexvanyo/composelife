# Module: dispatchers

This is a Kotlin Multiplatform library module responsible for providing Coroutine Dispatchers to the rest of the application.

## Purpose & Architecture

- This module centralizes the creation and provision of `CoroutineDispatcher` instances.
- It abstracts the underlying platform-specific dispatchers (`Dispatchers.Main`, `Dispatchers.IO`, etc.) behind a common interface, `ComposeLifeDispatchers`.
- This allows for better testability, as the dispatchers can be easily replaced with `TestDispatcher` instances in tests.
- It provides implementations for Android, JVM (Desktop), and WasmJs.

## Usage

- Other modules should depend on this module and inject the `ComposeLifeDispatchers` interface rather than using the global `Dispatchers` object directly.
- This ensures that all coroutine execution is managed consistently and can be controlled during testing.
