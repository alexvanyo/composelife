# Module: process-lifecycle

This module provides an injectable observer for the application's process lifecycle.

## Purpose & Architecture

- This is a Kotlin Multiplatform library module, primarily for Android.
- It wraps the `androidx.lifecycle:lifecycle-process` artifact to provide a `LifecycleOwner` for the entire application process.
- This allows components to observe when the application as a whole moves between states (e.g., comes to the foreground, goes to the background).
- By providing this as an injectable component, it makes testing easier and decouples components from the Android-specific static `ProcessLifecycleOwner`.

## Usage

- Inject the process `LifecycleOwner` from this module when you need to perform actions based on the lifecycle of the entire application, rather than a single `Activity` or `Fragment`.

## Key Dependencies

- `androidx.lifecycle:lifecycle-process`: The underlying AndroidX library that provides the process lifecycle.
- `:inject-scopes`: For dependency injection.
