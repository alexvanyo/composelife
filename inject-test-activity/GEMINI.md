# Module: inject-test-activity

This module provides a test `Activity` with dependency injection capabilities for instrumentation tests.

## Purpose & Architecture

- This is a Kotlin Multiplatform library module, primarily for Android testing.
- It combines the functionality of `:test-activity` and `:inject-test`.
- It provides a base `Activity` class for tests that comes pre-configured with a test dependency injection graph.
- This is useful for testing UI components or features that require both an `Activity` context and injected dependencies.

## Key Dependencies

- `:test-activity`: Provides the base test `Activity`.
- `:inject-test`: Provides the test dependency injection framework.
