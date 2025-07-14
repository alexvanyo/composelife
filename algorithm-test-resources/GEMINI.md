# Module: algorithm-test-resources

This module provides test resources for the `:algorithm` module.

## Purpose & Architecture

- This is a Kotlin Multiplatform library module.
- Its sole purpose is to hold test-only resources, such as sample data, patterns, or other files needed for testing the `:algorithm` module.
- This keeps the main `:algorithm` module clean from test-specific assets.

## Usage

- Test source sets in other modules (like `algorithm`'s own tests) can depend on this module to access the test resources.

See the [README.md](README.md) for more information.
