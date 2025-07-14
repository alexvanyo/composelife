# Module: database-test

This module provides test implementations and helpers for the `:database` module.

## Purpose & Architecture

- This is a Kotlin Multiplatform library module.
- It provides the necessary components to test database interactions in a controlled environment.
- It includes dependencies on test-specific coroutine libraries (`kotlinx-coroutines-test`) and the platform-specific SQLDelight drivers needed to run database tests on Android, Desktop (JVM), and WasmJs.
- This allows for writing tests that can interact with an in-memory or test-specific database instance.

## Usage

- Test source sets in other modules that need to test database functionality should depend on this module.
- It facilitates the creation of test-specific database instances for reliable and isolated testing.

## Key Dependencies

- `:database`: The main database module for which this provides test support.
- `kotlinx-coroutines-test`: For testing coroutine-based database queries.
- `sqldelight-android-driver`, `sqldelight-sqlite-driver`, `sqldelight-web-driver`: Platform-specific drivers for running SQLDelight in test environments.
