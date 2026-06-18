# Module: random

This module provides an injectable `Random` instance for the application.

## Purpose & Architecture

- This is a Kotlin Multiplatform library module.
- It abstracts the generation of random numbers behind an interface, allowing for dependency injection.
- The primary purpose is to enable deterministic testing of logic that relies on randomness. In tests, the real `Random` implementation can be replaced with a test double that produces a predictable sequence of numbers.
- The module targets Android, Desktop (JVM), and WasmJs platforms.

## Usage

- Any component that needs to generate random numbers should inject the `Random` object from this module rather than creating its own instance.

## Key Dependencies

- `:inject-scopes`: For dependency injection.
