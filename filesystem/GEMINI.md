# Module: filesystem

This is a Kotlin Multiplatform library module that provides a platform-agnostic abstraction for interacting with the file system.

## Purpose & Architecture

- This module uses the **Okio** library to provide a consistent API for file I/O across all supported platforms (Android, Desktop, WasmJs).
- It provides a pre-configured `FileSystem` object that should be used for all file operations.
- This approach avoids the need to write platform-specific code for reading and writing files.

## Usage

- When you need to read or write a file, inject and use the `FileSystem` object provided by this module.
- This is especially important for modules that need to store data, such as `:preferences` (which uses it for the DataStore backend) and `:database`.
- For testing, Okio provides a `FakeFileSystem` that allows for fast and reliable in-memory file system tests.
