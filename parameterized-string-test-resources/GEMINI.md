# Module: parameterized-string-test-resources

This module provides test resources for the `:parameterized-string` module.

## Purpose & Architecture

- This is a Kotlin Multiplatform library module.
- Its purpose is to hold test-only resources, such as sample `ParameterizedString` objects or other data needed for testing the `:parameterized-string` module.
- This keeps the main `:parameterized-string` module clean from test-specific assets.

## Usage

- The `androidSharedTest` source set in `:parameterized-string` depends on this module to access the test resources.
