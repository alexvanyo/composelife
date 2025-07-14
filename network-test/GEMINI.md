# Module: network-test

This module provides test implementations and helpers for the `:network` module.

## Purpose & Architecture

- This is a Kotlin Multiplatform library module.
- It provides the necessary components to test network interactions in a controlled environment.
- It uses the `ktor-client-mock` engine to mock HTTP requests and responses, allowing for hermetic testing of network-related code.
- This is crucial for writing fast, reliable, and deterministic tests for components that depend on the `:network` module.

## Usage

- Test source sets in other modules that need to test network functionality should depend on this module.
- It allows for defining expected network responses and verifying that the correct requests are made.

## Key Dependencies

- `:network`: The main network module for which this provides test support.
- `io.ktor:ktor-client-mock`: The core library for mocking Ktor HTTP clients.
