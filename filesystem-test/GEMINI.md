# Module: filesystem-test

This is a Kotlin Multiplatform library module that provides test implementations for the `:filesystem` module.

## Purpose & Architecture

- This module provides a `FakeFileSystem` from the Okio library, which is an in-memory file system that is useful
  for testing code that interacts with the file system.
- It allows for fast and reliable tests without needing to touch the actual file system on the host machine.

## Usage

- When writing tests for components that use the `FileSystem` from the `:filesystem` module, inject the
  `FakeFileSystem` from this module to control the file system environment and make assertions about file
  operations.
