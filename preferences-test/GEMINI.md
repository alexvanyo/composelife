# Module: preferences-test

This module provides test implementations and helpers for the `:preferences` module.

## Purpose & Architecture

- This is a Kotlin Multiplatform library module.
- It provides the necessary components to test the `:preferences` module in a controlled environment.
- It allows for creating test instances of the preferences DataStore, which can be backed by an in-memory file system.

## Usage

- Test source sets in other modules that need to test logic depending on user preferences should use the test helpers from this module.
- This allows for setting specific preference values for a test and verifying that the application logic reacts correctly.

## Key Dependencies

- `:preferences`: The main preferences module for which this provides test support.
- `:filesystem-test`: Provides a `FakeFileSystem` from Okio, allowing the DataStore to operate in-memory without touching the disk.
- `:dispatchers-test`: To provide test dispatchers for deterministic testing of coroutine-based preference flows.
- `:inject-test`: To provide test dependency injection components.
