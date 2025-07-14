# Module: data-test-resources

This module provides test resources for the `:data` module.

## Purpose & Architecture

- This is a Kotlin Multiplatform library module.
- Its purpose is to hold test-only resources, such as sample data, mock responses, or other files needed for testing the repositories in the `:data` module.
- This keeps the main `:data` module clean from test-specific assets.

## Usage

- Test source sets in other modules can depend on this module to access the test resources for data-layer testing.

See the [README.md](README.md) for more information.
